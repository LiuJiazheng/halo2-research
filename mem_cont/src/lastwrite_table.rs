use crate::memory_table::MemTableEntry;
use core::panic;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Selector, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

pub struct LastWriteTableChip<F: Field> {
    pub config: LastWriteTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct LastWriteTableConfig {
    // | addr | id | value |
    pub advice: [Column<Advice>; 3],
    // selector for region
    pub sel: Selector,
}

impl<F: Field> Chip<F> for LastWriteTableChip<F> {
    type Config = LastWriteTableConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: Field> LastWriteTableChip<F> {
    pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Configure the last write table
    /// memtbl_schema: [addr, id, value, is_last_write]
    /// last_write_schema: [addr, id, value, heritage]
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        memtbl_schema: [Column<Advice>; 4],
        memtbl_sel: Selector,
        last_write_schema: [Column<Advice>; 3],
        last_write_sel: Selector,
        binary_range: TableColumn,
    ) -> <Self as Chip<F>>::Config {
        // Enforce equality
        for col in memtbl_schema.iter() {
            meta.enable_equality(*col);
        }

        for col in last_write_schema.iter() {
            meta.enable_equality(*col);
        }

        // Load name of columns
        let (memtbl_addr, memtbl_id, memtbl_value, is_last_write) = if let [addr, id, value, is_last_write] =
            (0..4)
                .map(|i| memtbl_schema[i])
                .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value, is_last_write)
        } else {
            panic!("wrong match")
        };

        let (lw_addr, lw_id, lw_value) = if let [addr, id, value] = (0..3)
            .map(|i| last_write_schema[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        // Lookup Conditions:
        // is_last_write must be in binary range
        meta.lookup("memtbl col is_last_write", |meta| {
            let s = meta.query_selector(memtbl_sel);
            let is_last_write = meta.query_advice(is_last_write, Rotation::cur());

            vec![(s * is_last_write, binary_range)]
        });

        // Lookup Conditions:
        // For any row in lw table, it comes from a row in mem table
        meta.lookup_any("lw tbl belongs to memtbl", |meta| {
            let s = meta.query_selector(last_write_sel);
            let lw_addr = meta.query_advice(lw_addr, Rotation::cur());
            let lw_id = meta.query_advice(lw_id, Rotation::cur());
            let lw_value = meta.query_advice(lw_value, Rotation::cur());

            let memtbl_addr = meta.query_advice(memtbl_addr, Rotation::cur());
            let memtbl_id = meta.query_advice(memtbl_id, Rotation::cur());
            let memtbl_value = meta.query_advice(memtbl_value, Rotation::cur());

            vec![
                (s.clone() * lw_addr, memtbl_addr),
                (s.clone() * lw_id, memtbl_id),
                (s * lw_value, memtbl_value),
            ]
        });

        // Lookup Conditions:
        // For any row in mem table, and it is marked as 'last write', it must belong to a row in lw table
        // Thus, lw table is exact the extraction of mem table with 'last write' marked -- every last write entry from memtbl has
        // been present in lw table, and only once. The uniqueness of lw table entry is guaranteed by the uniqueness of last write entry of mem table
        meta.lookup_any("memtbl last write entry belongs to lw table", |meta| {
            let s = meta.query_selector(memtbl_sel);
            let memtbl_addr = meta.query_advice(memtbl_addr, Rotation::cur());
            let memtbl_id = meta.query_advice(memtbl_id, Rotation::cur());
            let memtbl_value = meta.query_advice(memtbl_value, Rotation::cur());
            let is_last_write = meta.query_advice(is_last_write, Rotation::cur());

            let lw_addr = meta.query_advice(lw_addr, Rotation::cur());
            let lw_id = meta.query_advice(lw_id, Rotation::cur());
            let lw_value = meta.query_advice(lw_value, Rotation::cur());

            vec![
                (s.clone() * memtbl_addr * is_last_write.clone(), lw_addr),
                (s.clone() * memtbl_id * is_last_write.clone(), lw_id),
                (s * memtbl_value * is_last_write, lw_value),
            ]
        });

        LastWriteTableConfig {
            advice: last_write_schema,
            sel: last_write_sel,
        }
    }

    pub fn assign_lwtbl_from_memtbl(
        &self,
        mut layouter: impl Layouter<F>,
        memtbl_entries: &[MemTableEntry<F>],
    ) -> Result<Vec<MemTableEntry<F>>, Error> {
        let config = &self.config;
        let (lw_addr, lw_id, lw_value) = if let [addr, id, value] = (0..3)
            .map(|i| config.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        let lw_tbl = memtbl_entries.clone().to_vec();

        // Allocate lwtbl based on the given entries
        let _ = layouter
            .assign_region(
                || "assign lw table",
                |mut region: Region<F>| {
                    for (i, entry) in memtbl_entries.iter().enumerate() {
                        let _cell_addr = region
                            .assign_advice(
                                || format!("{} addr", i),
                                lw_addr,
                                i,
                                || Value::known(entry.addr),
                            )
                            .unwrap();
                        let _cell_id = region
                            .assign_advice(
                                || format!("{} id", i),
                                lw_id,
                                i,
                                || Value::known(entry.id),
                            )
                            .unwrap();
                        let _cell_value = region
                            .assign_advice(
                                || format!("{} value", i),
                                lw_value,
                                i,
                                || Value::known(entry.value),
                            )
                            .unwrap();
                        config.sel.enable(&mut region, i)?;
                    }
                    Ok(())
                },
            )
            .unwrap();

        Ok(lw_tbl)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory_table::{MemTableChip, MemTableConfig};
    use crate::param::{MEM_RANGE_BITS, VALUE_RANGE_BITS};
    use halo2_proofs::circuit::SimpleFloorPlanner;
    use halo2_proofs::plonk::Circuit;
    use proptest::prelude::Rng;

    #[derive(Clone, Debug)]
    struct CircuitConfig {
        memtbl_config: MemTableConfig,
        lwtbl_config: LastWriteTableConfig,
    }

    #[derive(Default, Debug)]
    struct MinimalMemTable<F: Field> {
        entries: Vec<MemTableEntry<F>>,
    }

    impl<F> Circuit<F> for MinimalMemTable<F>
    where
        F: Field,
    {
        type Config = CircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            let memtbl_advice = [(); 6].map(|_| meta.advice_column());
            let range = [(); 3].map(|_| meta.lookup_table_column());
            let memtbl_sel = meta.complex_selector();

            let lw_advice = [(); 3].map(|_| meta.advice_column());
            let lw_sel = meta.complex_selector();
            // Reference memtbl schema
            // | addr | id | value | is_last_write |
            // Order really matters, latter we can make it several const
            let ref_memtbl_schema = [
                memtbl_advice[0],
                memtbl_advice[2],
                memtbl_advice[5],
                memtbl_advice[4],
            ];
            let binary_range = range[0];

            let memtbl_config = MemTableChip::configure(meta, memtbl_advice, range, memtbl_sel);
            let lwtbl_config = LastWriteTableChip::configure(
                meta,
                ref_memtbl_schema,
                memtbl_sel,
                lw_advice,
                lw_sel,
                binary_range,
            );

            CircuitConfig {
                memtbl_config,
                lwtbl_config,
            }
        }

        fn synthesize(
            &self,
            config: Self::Config,
            mut layouter: impl Layouter<F>,
        ) -> Result<(), Error> {
            // Get MemTableChip
            let memtbl_chip = MemTableChip::<F>::construct(config.memtbl_config);
            // Assign range
            memtbl_chip.assign_range(layouter.namespace(|| "assign range"))?;
            // Assign table
            let (lwtbl_from_memtbl, _) = memtbl_chip
                .assign_table(layouter.namespace(|| "assign table"), &self.entries)
                .unwrap();

            // Get LastWriteTableChip
            let lwtbl_chip = LastWriteTableChip::<F>::construct(config.lwtbl_config);

            // Assign lwtbl from memtbl
            lwtbl_chip.assign_lwtbl_from_memtbl(
                layouter.namespace(|| "assign lwtbl from memtbl"),
                &lwtbl_from_memtbl,
            )?;

            Ok(())
        }
    }

    #[test]
    fn test_lwtbl() {
        use halo2_proofs::dev::MockProver;
        use halo2curves::bn256::Fr;
        use rand_core::OsRng;

        // ANCHOR: test-circuit
        // The number of rows in our circuit cannot exceed 2^k. Since our example
        // circuit is very small, we can pick a very small value here.
        let k = 8;

        // Create an buffer
        let mut entries: Vec<MemTableEntry<Fr>> = vec![];

        // Prepare the private inputs to the circuit!
        let mut rng = OsRng;
        for id in 0..(1 << MEM_RANGE_BITS) {
            // we only genegate 6 addresses, by Pigeonhole principle there must be some addresses with more than one entry
            let addr = Fr::from(rng.gen_range(0..6) as u64);
            let value = Fr::from(rng.gen_range(0..(1 << VALUE_RANGE_BITS)) as u64);
            entries.push(MemTableEntry {
                addr,
                id: Fr::from(id as u64),
                value,
            });
        }

        // Sort the entries by address and then by id
        entries.sort_by(|a, b| {
            if a.addr == b.addr {
                a.id.cmp(&b.id)
            } else {
                a.addr.cmp(&b.addr)
            }
        });

        // Create the circuit
        let circuit = MinimalMemTable { entries };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
