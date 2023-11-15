use crate::lastwrite_table::{LastWriteTableChip, LastWriteTableConfig};
use crate::memory_table::{MemTableChip, MemTableConfig};
use crate::rtable::{RTableChip, RTableConfig};
use core::panic;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

struct ConcatTableChip<F: Field> {
    config: ConcatTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct ConcatTableConfig {
    joint_table_config: LastWriteTableConfig,
    left_sel: Selector,
    right_sel: Selector,
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

impl<F: Field> ConcatTableChip<F> {
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
        sels: [Selector; 2],
    ) -> <Self as Chip<F>>::Config {
        // Enable equality constraints for all columns in the advice table.
        for col in joint_table_config.advice.iter() {
            meta.enable_equality(*col);
        }
        // Load the selectors
        let joint_left_sel = sels[0];
        let joint_right_sel = sels[1];

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
        let (binary_range, memory_range, value_range) =
            destructure_buffer!(range_table, (binary_range, memory_range, value_range));

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

        // Final config
        ConcatTableConfig {
            joint_table_config,
            left_sel: joint_left_sel,
            right_sel: joint_right_sel,
        }
    }
}
