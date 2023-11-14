use core::panic;
use ff::PrimeField;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Chip, Layouter, Value, AssignedCell},
    plonk::{Advice, Expression, Column, ConstraintSystem, Error, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    lastwrite_table::LastWriteTableConfig, memory_table::MemTableEntry,
};

pub struct RTableChip<F: Field> {
    config: RTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct RTableConfig {
    /// The right table it records on
    pub rtable: LastWriteTableConfig,
    /// Is the entry in the right table overwritten by left table?
    /// Since we know left table is always the latest write
    pub overwrite: Column<Advice>,
    /// Eid boundary
    pub eid_boundary: Column<Advice>,
}

impl<F: Field> Chip<F> for RTableChip<F> {
    type Config = RTableConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: Field + std::cmp::Ord + PrimeField> RTableChip<F> {
    pub fn construct(config: RTableConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        ref_ltable: &LastWriteTableConfig,
        rtable: LastWriteTableConfig,
        overwrite: Column<Advice>,
        eid_boundary: Column<Advice>,
        ranges: [TableColumn; 3],
    ) -> <Self as Chip<F>>::Config {
        for col in rtable.advice.iter() {
            meta.enable_equality(*col);
        }
        meta.enable_equality(overwrite);
        meta.enable_equality(eid_boundary);

        // Load names of left table columns
        let left_addr = ref_ltable.advice[0];

        // Load names of right table columns
        let (right_addr, right_id, right_value) = if let [addr, id, value] = (0..3)
            .map(|i| rtable.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        // Load names of range columns
        let (binary_range, memory_range, value_range) = if let [binary, memory, value] =
            (0..3).map(|i| ranges[i]).collect::<Vec<TableColumn>>()[..]
        {
            (binary, memory, value)
        } else {
            panic!("wrong match")
        };

        // Load names of selectors
        let right_sel = rtable.sel;

        // Common constraints
        meta.lookup(format!("right addr"), |meta| {
            let s = meta.query_selector(right_sel);
            let addr = meta.query_advice(right_addr, Rotation::cur());

            vec![(s * addr, memory_range)]
        });

        meta.lookup(format!("right id"), |meta| {
            let s = meta.query_selector(right_sel);
            let id = meta.query_advice(right_id, Rotation::cur());

            vec![(s * id, memory_range)]
        });

        meta.lookup(format!("right value"), |meta| {
            let s = meta.query_selector(right_sel);
            let value = meta.query_advice(right_value, Rotation::cur());

            vec![(s * value, value_range)]
        });

        meta.lookup("overrite bit", |meta| {
            let s = meta.query_selector(right_sel);
            let overwrite = meta.query_advice(overwrite, Rotation::cur());

            vec![(s * overwrite, binary_range)]
        });

        // eid constraints
        // Right table is, semanticlly, the 'previous last write table'. So it possesses:
        // For any entry x in rtable, x.eid < eid from memtbl
        // Namely the minial eid of memtbl. Since memtbl is sorted, it must be first one
        meta.lookup(format!("right eid"), |meta| {
            let s = meta.query_selector(right_sel);
            let eid_boundary = meta.query_advice(eid_boundary, Rotation::cur());
            let right_id = meta.query_advice(right_id, Rotation::cur());

            vec![(s * (eid_boundary - right_id - Expression::Constant(F::ONE)), memory_range)]
        });

        // Overwrite constraints
        // There is a chance that if left table may also contain the same addr as right table, thus
        // the right table entry shall be fully overwritten
        // Overrite = 1 => for any entry, exists y in left table, y.addr = x.addr (Sufficient)
        // Overrite = 0 => for any entry, there is no such y in left table, y.addr = x.addr (Necessary)
        // It is hard to prove the necessary condition in this part, we will postpone it until in final
        // concat table by proving the unqueness of addr, to infer the necessary condition. The core reason
        // is Halo2 poly constraint only enforce a form of `expression == 0` while asserts on `expression != 0`
        // In short, this shows "no extra entry can be faked as left table entry if it is not" / "no more"
        // We still need to prove "no less", meaning all entries with address in left table has been marked as one
        meta.lookup_any("overwrite sufficiency", |meta| {
            let s = meta.query_selector(right_sel);
            let overwrite = meta.query_advice(overwrite, Rotation::cur());
            let left_addr = meta.query_advice(left_addr, Rotation::cur());
            let right_addr = meta.query_advice(right_addr, Rotation::cur());

            vec![(s * overwrite * right_addr, left_addr)]
        });

        RTableConfig {
            rtable,
            overwrite,
            eid_boundary,
        }
    }

    /// left table is `current_last_write_table` and
    /// right table is `previous_last_write_table`
    pub fn assign_rtable(
        &self,
        mut layouter: impl Layouter<F>,
        previous_last_write_table: &[MemTableEntry<F>],
        current_last_write_table: &[MemTableEntry<F>],
        eid_maximal: AssignedCell<F,F>,
    ) -> Result<Vec<MemTableEntry<F>>, Error> {
        // Set up columns names
        let config = self.config();
        let (addr, id, value) = if let [addr, id, value] = (0..3)
            .map(|i| config.rtable.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };
        let sel = config.rtable.sel;
        let overwrite = config.overwrite;
        let eid_boundary = config.eid_boundary;

        // Set up lookup btree
        let mut lookup = std::collections::BTreeMap::new();
        for entry in current_last_write_table.iter() {
            lookup.insert(entry.addr, 1 as u128);
        }

        macro_rules! lookup_addr {
            ($addr:expr) => {
                lookup.get(&$addr).copied().unwrap_or(0) as u128
            };
        }

        let mut rtable = vec![];

        let _ = layouter.assign_region(
            || "assign rtable",
            |mut region| {
                for (i, entry) in previous_last_write_table.iter().enumerate() {
                    sel.enable(&mut region, i)?;
                    let _ = region.assign_advice(
                        || "assign addr",
                        addr,
                        i,
                        || Value::known(entry.addr),
                    )?;
                    let _ =
                        region.assign_advice(|| "assign id", id, i, || Value::known(entry.id))?;
                    let _ = region.assign_advice(
                        || "assign value",
                        value,
                        i,
                        || Value::known(entry.value),
                    )?;
                    let _ = region.assign_advice(
                        || "assign overwrite",
                        overwrite,
                        i,
                        || Value::known(F::from_u128(lookup_addr!(entry.addr))),
                    )?;
                    let _ = eid_maximal.copy_advice(||"copy eid boudary", &mut region, eid_boundary, i)?;

                    if lookup_addr!(entry.addr) == 0 {
                        rtable.push(entry.clone());
                    }
                }
                Ok(())
            },
        );

        // Assign would be called twice
        assert!(rtable.len() % 2 == 0);
        rtable.truncate(rtable.len() / 2);

        Ok(rtable)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::memory_table::{MemTableChip, MemTableConfig};
    use crate::lastwrite_table::{LastWriteTableChip, LastWriteTableConfig};
    use crate::param::VALUE_RANGE_BITS;
    use halo2_proofs::circuit::SimpleFloorPlanner;
    use halo2_proofs::plonk::Circuit;
    use proptest::prelude::Rng;

    #[derive(Clone, Debug)]
    struct CircuitConfig {
        memtbl_config: MemTableConfig,
        lwtbl_config: LastWriteTableConfig,
        rtbl_config: RTableConfig,
    }

    #[derive(Default, Debug)]
    struct MinimalMemTable<F: Field> {
        entries: Vec<MemTableEntry<F>>,
        previous_last_write_table: Vec<MemTableEntry<F>>,
    }

    impl<F> Circuit<F> for MinimalMemTable<F>
    where
        F: Field + PrimeField + std::cmp::Ord,
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
            let ranges = [(); 3].map(|_| meta.lookup_table_column());
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
            let binary_range = ranges[0];

            let memtbl_config = MemTableChip::configure(meta, memtbl_advice, ranges, memtbl_sel);
            let lwtbl_config = LastWriteTableChip::configure(
                meta,
                ref_memtbl_schema,
                memtbl_sel,
                lw_advice,
                lw_sel,
                binary_range,
            );

            let rtbl_advice = [(); 3].map(|_| meta.advice_column());
            let rtbl_sel = meta.complex_selector();
            let rtbl_overwrite = meta.advice_column();
            let rtbl_eid_boundary = meta.advice_column();
            let rtbl_config = RTableChip::configure(
                meta,
                &lwtbl_config,
                LastWriteTableConfig {
                    advice: rtbl_advice,
                    sel: rtbl_sel,
                },
                rtbl_overwrite,
                rtbl_eid_boundary,
                ranges,
            );

            CircuitConfig {
                memtbl_config,
                lwtbl_config,
                rtbl_config,
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
            let (lwtbl_from_memtbl, cells) = memtbl_chip
                .assign_table(layouter.namespace(|| "assign table"), &self.entries)
                .unwrap();

            // Get LastWriteTableChip
            let lwtbl_chip = LastWriteTableChip::<F>::construct(config.lwtbl_config);

            // Assign lwtbl from memtbl
            let cur_lwtbl = lwtbl_chip.assign_lwtbl_from_memtbl(
                layouter.namespace(|| "assign lwtbl from memtbl"),
                &lwtbl_from_memtbl,
            )?;

            // Get rtable chip
            let rtbl_chip = RTableChip::<F>::construct(config.rtbl_config);
            let _extracted_rtable = rtbl_chip.assign_rtable(
                layouter.namespace(|| "assign rtable"),
                &self.previous_last_write_table,
                &cur_lwtbl,
                cells[0].id.clone(),
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
        let local_range_bits = 3;

        // Create an buffer
        let mut entries: Vec<MemTableEntry<Fr>> = vec![];

        // Prepare the private inputs to the circuit!
        let mut rng = OsRng;
        for id in 0..(1 << local_range_bits) {
            // we only genegate 6 addresses, by Pigeonhole principle there must be some addresses with more than one entry
            let addr = Fr::from(rng.gen_range(0..6) as u64);
            let value = Fr::from(rng.gen_range(0..(1 << VALUE_RANGE_BITS)) as u64);
            entries.push(MemTableEntry {
                addr,
                id: Fr::from( (1<< local_range_bits) + id as u64),
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

        // Prepare previous last write table
        let mut previous_last_write_table: Vec<MemTableEntry<Fr>> = vec![];
        for id in 0..((1 << local_range_bits) - 1){
            let addr = Fr::from(id as u64);
            let value = Fr::from(rng.gen_range(0..(1 << VALUE_RANGE_BITS)) as u64);
            previous_last_write_table.push(MemTableEntry {
                addr,
                id: Fr::from(id as u64),
                value,
            });
        }

        // Create the circuit
        let circuit = MinimalMemTable { entries, previous_last_write_table };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}