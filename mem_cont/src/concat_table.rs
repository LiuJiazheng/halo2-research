use crate::lastwrite_table::LastWriteTableConfig;
use crate::memory_table::MemTableEntry;
use crate::rtable::RTableConfig;
use core::panic;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Chip, Layouter, Value},
    plonk::{ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

pub struct ConcatTableChip<F: Field> {
    pub config: ConcatTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct ConcatTableConfig {
    pub joint_table_config: LastWriteTableConfig,
    pub left_sel: Selector,
}

impl<F: Field> Chip<F> for ConcatTableChip<F> {
    type Config = ConcatTableConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: Field + std::cmp::Ord> ConcatTableChip<F> {
    pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        ref_left_table_config: &LastWriteTableConfig,
        ref_right_table_config: &RTableConfig,
        joint_table_config: LastWriteTableConfig,
        range_table: [TableColumn; 3],
        joint_left_sel: Selector,
    ) -> <Self as Chip<F>>::Config {
        // Enable equality constraints for all columns in the advice table.
        for col in joint_table_config.advice.iter() {
            meta.enable_equality(*col);
        }
        // Load the selector
        let total_sel = joint_table_config.sel;

        // Load the overwrite flag
        let overwrite = ref_right_table_config.overwrite;

        // Load the names of each table
        let (joint_addr, joint_id, joint_value) =
            destructure_buffer!(joint_table_config.advice, (addr, id, value));
        let (left_addr, left_id, left_value) = destructure_buffer!(
            ref_left_table_config.advice,
            (left_addr, left_id, left_value)
        );
        let (right_addr, right_id, right_value) = destructure_buffer!(
            ref_right_table_config.rtable.advice,
            (right_addr, right_id, right_value)
        );
        let (_, memory_range, _) =
            destructure_buffer!(range_table, (binary_range, memory_range, value_range));

        // Gate
        // Need to make sure two selectors, total_sel 'covers' left_sel
        // TOTAL_SEL  LEFT_SEL  VALUE
        //   1          1         0
        //   1          0         0
        //   0          1         1
        //   0          0         0
        // Because in this proof system, 0 is SAT and non-zero is UNSAT
        // Based on this truth table, we have NOT(TOTAL_SEL) AND LEFT_SEL
        meta.create_gate("total_sel covers left_sel", |meta| {
            let total_sel = meta.query_selector(total_sel);
            let left_sel = meta.query_selector(joint_left_sel);
            let one = Expression::Constant(F::ONE);

            vec![(one - total_sel) * left_sel]
        });

        // Lookup
        // All left table are coming to the joint table
        meta.lookup_any("left table comes to joint table", |meta| {
            let left_addr = meta.query_advice(left_addr, Rotation::cur());
            let left_id = meta.query_advice(left_id, Rotation::cur());
            let left_value = meta.query_advice(left_value, Rotation::cur());
            let joint_addr = meta.query_advice(joint_addr, Rotation::cur());
            let joint_id = meta.query_advice(joint_id, Rotation::cur());
            let joint_value = meta.query_advice(joint_value, Rotation::cur());
            let left_sel = meta.query_selector(ref_left_table_config.sel);

            vec![
                (left_sel.clone() * left_addr, joint_addr),
                (left_sel.clone() * left_id, joint_id),
                (left_sel * left_value, joint_value),
            ]
        });

        // Lookup
        // All right table entries with overwrite flag NOT SET shall be copied to the joint table
        meta.lookup_any("right table not overwrite", |meta| {
            let right_addr = meta.query_advice(right_addr, Rotation::cur());
            let right_id = meta.query_advice(right_id, Rotation::cur());
            let right_value = meta.query_advice(right_value, Rotation::cur());
            let joint_addr = meta.query_advice(joint_addr, Rotation::cur());
            let joint_id = meta.query_advice(joint_id, Rotation::cur());
            let joint_value = meta.query_advice(joint_value, Rotation::cur());
            let right_sel = meta.query_selector(ref_right_table_config.rtable.sel);
            let overwrite = meta.query_advice(overwrite, Rotation::cur());
            let one = Expression::Constant(F::ONE);

            vec![
                (
                    right_sel.clone() * (one.clone() - overwrite.clone()) * right_addr,
                    joint_addr,
                ),
                (
                    right_sel.clone() * (one.clone() - overwrite.clone()) * right_id,
                    joint_id,
                ),
                (right_sel * (one - overwrite) * right_value, joint_value),
            ]
        });

        // Lookup
        // When left sel on, joint table shall belong to left table
        meta.lookup_any("joint table's left part", |meta| {
            let joint_addr = meta.query_advice(joint_addr, Rotation::cur());
            let joint_id = meta.query_advice(joint_id, Rotation::cur());
            let joint_value = meta.query_advice(joint_value, Rotation::cur());
            let joint_left_sel = meta.query_selector(joint_left_sel);
            let left_addr = meta.query_advice(left_addr, Rotation::cur());
            let left_id = meta.query_advice(left_id, Rotation::cur());
            let left_value = meta.query_advice(left_value, Rotation::cur());

            vec![
                (joint_left_sel.clone() * joint_addr, left_addr),
                (joint_left_sel.clone() * joint_id, left_id),
                (joint_left_sel * joint_value, left_value),
            ]
        });

        // Lookup
        // When right sel on, joint table shall belong to right table (overwrite flag is not set)
        meta.lookup_any("joint table's right part", |meta| {
            let joint_addr = meta.query_advice(joint_addr, Rotation::cur());
            let joint_id = meta.query_advice(joint_id, Rotation::cur());
            let joint_value = meta.query_advice(joint_value, Rotation::cur());
            let joint_right_sel =
                meta.query_selector(total_sel) - meta.query_selector(joint_left_sel);
            let right_addr = meta.query_advice(right_addr, Rotation::cur());
            let right_id = meta.query_advice(right_id, Rotation::cur());
            let right_value = meta.query_advice(right_value, Rotation::cur());
            let overwrite = meta.query_advice(overwrite, Rotation::cur());
            let one = Expression::Constant(F::ONE);

            vec![
                (
                    joint_right_sel.clone() * joint_addr,
                    (one.clone() - overwrite.clone()) * right_addr,
                ),
                (
                    joint_right_sel.clone() * joint_id,
                    (one.clone() - overwrite.clone()) * right_id,
                ),
                (
                    joint_right_sel * joint_value,
                    (one - overwrite) * right_value,
                ),
            ]
        });

        // Lookup
        // To prove joint table with unique addr, we have to prove it stricly sorted (partial order)
        // By leveraging total_sel, we have to make sure the joint table has a bottom padding otherwise
        // this is going to violate
        meta.lookup("joint table's addr is sorted", |meta| {
            let addr = meta.query_advice(joint_addr, Rotation::cur());
            let addr_next = meta.query_advice(joint_addr, Rotation::next());
            let sel = meta.query_selector(total_sel);
            let one = Expression::Constant(F::ONE);

            vec![(sel * (addr_next - addr - one), memory_range)]
        });

        // Final config
        ConcatTableConfig {
            joint_table_config,
            left_sel: joint_left_sel,
        }
    }

    pub fn concat(
        &self,
        mut layouter: impl Layouter<F>,
        left_table: Vec<MemTableEntry<F>>,
        right_table: Vec<MemTableEntry<F>>,
    ) -> Result<(), Error> {
        let config = self.config();
        // Transfer (MemoryTable, isLeftTable)
        let left_table = left_table.iter().map(|x| (x, true));
        let right_table = right_table.iter().map(|x| (x, false));
        let mut joint_table = left_table.chain(right_table).collect::<Vec<_>>();
        // Sort the joint table by address and then by id
        // Ideally there shall be no duplicate address so there is no need to check id
        // But we do not do any check on a synthese related function
        joint_table.sort_by(|a, b| {
            if a.0.addr == b.0.addr {
                a.0.id.cmp(&b.0.id)
            } else {
                a.0.addr.cmp(&b.0.addr)
            }
        });
        // Debug
        for tuple in joint_table.iter() {
            let (entry, is_left_table) = tuple;
            println!(
                "addr: {:?}, id: {:?}, value: {:?}, is_left_table: {}",
                entry.addr, entry.id, entry.value, is_left_table
            );
        }
        // Load names from config
        let (joint_addr, joint_id, joint_value) =
            destructure_buffer!(config.joint_table_config.advice, (addr, id, value));
        let joint_left_sel = config.left_sel;
        let total_sel = config.joint_table_config.sel;
        // Assign the joint table
        layouter.assign_region(
            || "assign concat table",
            |mut region| {
                for (i, tuple) in joint_table.iter().enumerate() {
                    let (entry, is_left_table) = tuple;
                    let is_left_table = *is_left_table;

                    // Enable the region selector
                    total_sel.enable(&mut region, i)?;
                    // If it comes from left table, enable the left selector
                    if is_left_table {
                        joint_left_sel.enable(&mut region, i)?;
                    }
                    // Assign the address
                    region.assign_advice(
                        || "assign addr",
                        joint_addr,
                        i,
                        || Value::known(entry.addr),
                    )?;
                    // Assign the id
                    region.assign_advice(|| "assign id", joint_id, i, || Value::known(entry.id))?;
                    // Assign the value
                    region.assign_advice(
                        || "assign value",
                        joint_value,
                        i,
                        || Value::known(entry.value),
                    )?;
                }
                // bottom padding, since we have to prove the joint table is strictly sorted
                if !joint_table.is_empty() {
                    // Assign the address
                    // Normally the memory address's upper limit is less than size of Fp
                    // Should not be too worried about overflow on addr padding
                    region.assign_advice(
                        || "assign bottom padding addr",
                        joint_addr,
                        joint_table.len(),
                        || Value::known(joint_table.last().unwrap().0.addr + F::ONE),
                    )?;
                    // Assign the id
                    region.assign_advice(
                        || "assign bottom padding id",
                        joint_id,
                        joint_table.len(),
                        || Value::known(F::ZERO),
                    )?;
                    // Assign the value
                    region.assign_advice(
                        || "assign bottom padding value",
                        joint_value,
                        joint_table.len(),
                        || Value::known(F::ZERO),
                    )?;
                }
                Ok(())
            },
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lastwrite_table::{LastWriteTableChip, LastWriteTableConfig};
    use crate::memory_table::{MemTableChip, MemTableConfig};
    use crate::param::{MEM_RANGE_BITS, VALUE_RANGE_BITS};
    use crate::rtable::RTableChip;
    use halo2_proofs::circuit::SimpleFloorPlanner;
    use halo2_proofs::plonk::Circuit;
    use proptest::prelude::Rng;

    #[derive(Clone, Debug)]
    struct CircuitConfig {
        memtbl_config: MemTableConfig,
        lwtbl_config: LastWriteTableConfig,
        rtbl_config: RTableConfig,
        concat_config: ConcatTableConfig,
    }

    #[derive(Default, Debug)]
    struct MinimalMemTable<F: Field> {
        entries: Vec<MemTableEntry<F>>,
        previous_last_write_table: Vec<MemTableEntry<F>>,
    }

    impl<F> Circuit<F> for MinimalMemTable<F>
    where
        F: Field + ff::PrimeField + std::cmp::Ord,
    {
        type Config = CircuitConfig;
        type FloorPlanner = SimpleFloorPlanner;
        #[cfg(feature = "circuit-params")]
        type Params = ();

        fn without_witnesses(&self) -> Self {
            Self::default()
        }

        fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
            // Memtbl Config
            let memtbl_advice = [(); 6].map(|_| meta.advice_column());
            let ranges = [(); 3].map(|_| meta.lookup_table_column());
            let memtbl_sel = meta.complex_selector();
            let memtbl_config = MemTableChip::configure(meta, memtbl_advice, ranges, memtbl_sel);

            // Lwtbl Config
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

            let lwtbl_config = LastWriteTableChip::configure(
                meta,
                ref_memtbl_schema,
                memtbl_sel,
                lw_advice,
                lw_sel,
                binary_range,
            );

            // Rtbl Config
            let rtbl_advice = [(); 3].map(|_| meta.advice_column());
            let rtbl_sel = meta.complex_selector();
            let rtbl_overwrite = meta.advice_column();
            let rtbl_config = RTableChip::configure(
                meta,
                &lwtbl_config,
                LastWriteTableConfig {
                    advice: rtbl_advice,
                    sel: rtbl_sel,
                },
                rtbl_overwrite,
                ranges,
            );

            // Concat Config
            let joint_advice = [(); 3].map(|_| meta.advice_column());
            let joint_sel = meta.complex_selector();
            let left_sel = meta.complex_selector();
            let joint_table = LastWriteTableChip::<F>::new(&joint_advice, &joint_sel);
            let concat_config = ConcatTableChip::configure(
                meta,
                &lwtbl_config,
                &rtbl_config,
                joint_table,
                ranges,
                left_sel,
            );

            CircuitConfig {
                memtbl_config,
                lwtbl_config,
                rtbl_config,
                concat_config,
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
            let lwtbl_from_memtbl = memtbl_chip
                .assign_table(layouter.namespace(|| "assign table"), &self.entries)
                .unwrap();

            println!("-----------memtbl-------------------");
            for entry in self.entries.iter() {
                println!(
                    "addr: {:?}, id: {:?}, value: {:?}",
                    entry.addr, entry.id, entry.value
                );
            }
            println!("-------------------------------------");

            // Get LastWriteTableChip
            let lwtbl_chip = LastWriteTableChip::<F>::construct(config.lwtbl_config);
            // Assign lwtbl from memtbl
            let cur_lwtbl = lwtbl_chip.assign_lwtbl_from_memtbl(
                layouter.namespace(|| "assign lwtbl from memtbl"),
                &lwtbl_from_memtbl,
            )?;

            println!("-----------lwtbl-------------------");
            for entry in cur_lwtbl.iter() {
                println!(
                    "addr: {:?}, id: {:?}, value: {:?}",
                    entry.addr, entry.id, entry.value
                );
            }
            println!("-------------------------------------");

            // Get rtable chip
            let rtbl_chip = RTableChip::<F>::construct(config.rtbl_config);
            let extracted_rtable = rtbl_chip.assign_rtable(
                layouter.namespace(|| "assign rtable"),
                &self.previous_last_write_table,
                &cur_lwtbl,
            )?;
            println!("-----------previous_lwtbl-------------------");
            for entry in self.previous_last_write_table.iter() {
                println!(
                    "addr: {:?}, id: {:?}, value: {:?}",
                    entry.addr, entry.id, entry.value
                );
            }
            println!("-------------------------------------");

            println!("-----------rtable-------------------");
            for entry in extracted_rtable.iter() {
                println!(
                    "addr: {:?}, id: {:?}, value: {:?}",
                    entry.addr, entry.id, entry.value
                );
            }
            println!("-------------------------------------");

            // Get concat chip
            let concat_chip = ConcatTableChip::<F>::construct(config.concat_config);
            concat_chip.concat(
                layouter.namespace(|| "assign concat table"),
                cur_lwtbl,
                extracted_rtable,
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
        let local_range_bits = MEM_RANGE_BITS - 1;

        // Create an buffer
        let mut entries: Vec<MemTableEntry<Fr>> = vec![];

        // Prepare the private inputs to the circuit!
        let mut rng = OsRng;

        // Prepare previous last write table
        let mut previous_last_write_table: Vec<MemTableEntry<Fr>> = vec![];
        for id in 0..(1 << local_range_bits) {
            // As last write table, address shall be different
            let addr = Fr::from(id as u64);
            let id = Fr::from(id as u64);
            let value = Fr::from(rng.gen_range(0..(1 << VALUE_RANGE_BITS)) as u64);
            previous_last_write_table.push(MemTableEntry { addr, id, value });
        }

        // Then current memory table as primary witness
        for id in (1 << local_range_bits)..(1 << MEM_RANGE_BITS) {
            // we only genegate 4 addresses, by Pigeonhole principle there must be some addresses with more than one entry
            let addr = Fr::from(rng.gen_range(0..4) as u64);
            let id = Fr::from(id as u64);
            let value = Fr::from(rng.gen_range(0..(1 << VALUE_RANGE_BITS)) as u64);
            entries.push(MemTableEntry { addr, id, value });
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
        let circuit = MinimalMemTable {
            entries,
            previous_last_write_table,
        };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
