use core::panic;
use ff::PrimeField;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{layouter, AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

use crate::{
    lastwrite_table::LastWriteTableConfig, memory_table::MemTableEntry,
    memory_table::MemTableEntryCell,
};

pub struct RTableChip<F: Field> {
    config: RTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct RTableConfig {
    /// The left table it refers to
    pub ref_ltable: LastWriteTableConfig,
    /// The right table it records on
    pub rtable: LastWriteTableConfig,
    /// Is the entry in the right table overwritten by left table?
    /// Since we know left table is always the latest write
    pub overwrite: Column<Advice>,
    /// Common ranges being looked up
    pub ranges: [TableColumn; 3],
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
        ref_ltable: LastWriteTableConfig,
        rtable: LastWriteTableConfig,
        overwrite: Column<Advice>,
        ranges: [TableColumn; 3],
    ) -> <Self as Chip<F>>::Config {
        for col in rtable.advice.iter() {
            meta.enable_equality(*col);
        }

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
        let left_sel = ref_ltable.sel;
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
            ref_ltable,
            rtable,
            overwrite,
            ranges,
        }
    }

    /// left table is `current_last_write_table` and
    /// right table is `previous_last_write_table`
    pub fn assign_rtable(
        &self,
        mut layouter: impl Layouter<F>,
        previous_last_write_table: &[MemTableEntry<F>],
        current_last_write_table: &[MemTableEntry<F>],
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

                    if lookup_addr!(entry.addr) == 1 {
                        rtable.push(entry.clone());
                    }
                }
                Ok(())
            },
        );

        // Assign would be called twice
        assert!(rtable.len() / 2 == 0);
        rtable.truncate(rtable.len() / 2);

        Ok(rtable)
    }
}
