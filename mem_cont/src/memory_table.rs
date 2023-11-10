use crate::param::{MEM_RANGE_BITS, VALUE_RANGE_BITS};
use core::panic;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{AssignedCell, Chip, Layouter, Region, Value},
    plonk::{Advice, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use std::marker::PhantomData;

pub struct MemTableChip<F: Field> {
    pub config: MemTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
pub struct MemTableConfig {
    // | addr | addr_delta_inv | id | is_access_type_init | is_access_type_last_write | value |
    pub advice: [Column<Advice>; 6],
    // | binary_range | memory_range | value_range |
    pub range: [TableColumn; 3],
    // Selector for region
    pub sel: Selector,
    // Selector for init row
    pub init_sel: Selector,
}

impl<F: Field> Chip<F> for MemTableChip<F> {
    type Config = MemTableConfig;
    type Loaded = ();

    fn config(&self) -> &Self::Config {
        &self.config
    }

    fn loaded(&self) -> &Self::Loaded {
        &()
    }
}

impl<F: Field> MemTableChip<F> {
    pub fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// In MemTableConfig, we will constrain the following:
    /// r(cur).address == r(next).address => r(cur).id <= r(next).id
    /// r(cur).address != r(next).address <=> r(cur).access_type == last_write
    /// r(cur).address != r(next).address <=> r(next).access_type == init
    /// r(cur).address != r(next).address <=> r(cur).address < r(next).address
    /// Semenatically, it is a sort table, primary key is address, secondary key is id
    /// When address is different, last entry from previous group of address must be last write, and first enrty of next group of address must be init
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        advice: [Column<Advice>; 6],
        range: [TableColumn; 3],
        sel: Selector,
    ) -> <Self as Chip<F>>::Config {
        for col in advice.iter() {
            meta.enable_equality(*col);
        }

        let (addr, addr_delta_inv, id, is_access_type_init, is_access_type_last_write, value) =
            if let [addr, addr_delta_inv, id, is_access_type_init, is_access_type_last_write, value] =
                (0..6).map(|i| advice[i]).collect::<Vec<Column<Advice>>>()[..]
            {
                (
                    addr,
                    addr_delta_inv,
                    id,
                    is_access_type_init,
                    is_access_type_last_write,
                    value,
                )
            } else {
                panic!("wrong match")
            };
        let (binary_range, memory_range, value_range) = if let [binary_range, memory_range, value_range] =
            (0..3).map(|i| range[i]).collect::<Vec<TableColumn>>()[..]
        {
            (binary_range, memory_range, value_range)
        } else {
            panic!("wrong match")
        };

        // Sel_selector is only used within this chip
        let init_sel = meta.complex_selector();

        // Lookup Conditions:
        // 1. Init selector shall show ONCE and ONLY ONCE
        // 2. Col acc_init_bit must be {0,1}
        // 3. Col acc_last_write_bit must be {0,1}
        // 4. id must be in memory range (for now)
        // 5. value must be in value range
        // 6. addr must be in memory range
        // 7. If addr_bit == 1, r(cur).id <= r(next).id
        // 8. If addr_bit == 0, r(cur).addr < r(next).addr
        // Cannot do a federal query since the tuple (a,b,c...) is not in the lookup table (bianry_range, binary_range, memorary_range...)
        // Each one should be a separate query

        // Since selectors are all from {0, 1}
        meta.lookup_any("memory table range check 1 init once only once", |meta| {
            let init_s = meta.query_selector(init_sel);
            let s = meta.query_selector(sel);
            let one = Expression::Constant(F::ONE);

            // init sel shows once
            vec![(one, init_s * s)]
        });

        meta.lookup(
            "memory table range check 2: acc_init_bit must be {0,1}",
            |meta| {
                let s = meta.query_selector(sel);
                let acc_init_bit = meta.query_advice(is_access_type_init, Rotation::next());

                vec![(s * acc_init_bit, binary_range)]
            },
        );

        meta.lookup(
            "memory table range check 3: acc_last_write_bit must be {0,1}",
            |meta| {
                let s = meta.query_selector(sel);
                let acc_last_write_bit =
                    meta.query_advice(is_access_type_last_write, Rotation::cur());

                vec![(s * acc_last_write_bit, binary_range)]
            },
        );

        meta.lookup(
            "memory table range check 4: id must be in memory range",
            |meta| {
                let s = meta.query_selector(sel);
                let cur_id = meta.query_advice(id, Rotation::cur());

                vec![(s * cur_id, memory_range)]
            },
        );

        meta.lookup(
            "memory table range check 5: value must be in value range",
            |meta| {
                let s = meta.query_selector(sel);
                let value = meta.query_advice(value, Rotation::cur());

                vec![(s * value, value_range)]
            },
        );

        meta.lookup(
            "memory table range check 6: addr must be in memory range",
            |meta| {
                let s = meta.query_selector(sel);
                let cur_addr = meta.query_advice(addr, Rotation::cur());

                vec![(s * cur_addr, memory_range)]
            },
        );

        meta.lookup(
            "memory table range check 7: same address, id check",
            |meta| {
                // Query selector
                let s = meta.query_selector(sel);
                // Get the detla of id
                let cur_id = meta.query_advice(id, Rotation::cur());
                let next_id = meta.query_advice(id, Rotation::next());
                let delta_id = next_id - cur_id.clone();
                // Query delta of address
                let cur_addr = meta.query_advice(addr, Rotation::cur());
                let next_addr = meta.query_advice(addr, Rotation::next());
                let delta_addr = next_addr - cur_addr;
                // Query inverse of delta of address
                let delta_addr_inv = meta.query_advice(addr_delta_inv, Rotation::next());
                // Is zero bit
                let is_zero_bit =
                    Expression::Constant(F::ONE) - delta_addr.clone() * delta_addr_inv;

                vec![(s * is_zero_bit * delta_id, memory_range)]
            },
        );

        meta.lookup(
            "memory table range check 8: different address, address stricly ascent",
            |meta| {
                // Query selector
                let s = meta.query_selector(sel);
                // Get the delta between the current address and the next address
                let cur_addr = meta.query_advice(addr, Rotation::cur());
                let next_addr = meta.query_advice(addr, Rotation::next());
                let delta_addr = next_addr - cur_addr.clone();
                // Query inverse of delta of address
                let delta_addr_inv = meta.query_advice(addr_delta_inv, Rotation::next());
                // Prepare constant
                let one = Expression::Constant(F::ONE);
                // Is zero bit
                let is_zero_bit = one.clone() - delta_addr.clone() * delta_addr_inv;

                vec![(
                    s * (one.clone() - is_zero_bit) * (delta_addr - one),
                    memory_range,
                )]
            },
        );

        meta.create_gate("memory table gate constraint", |meta| {
            let s = meta.query_selector(sel);
            // Get the delta between the current address and the next address
            let cur_addr = meta.query_advice(addr, Rotation::cur());
            let next_addr = meta.query_advice(addr, Rotation::next());
            let delta_addr = next_addr - cur_addr;

            // Query inverse of delta of address
            let delta_addr_inv = meta.query_advice(addr_delta_inv, Rotation::next());
            // Prepare constant
            let one = Expression::Constant(F::ONE);
            // Is zero bit
            let is_zero_bit = one.clone() - delta_addr.clone() * delta_addr_inv;
            // Query bits
            let acc_init_bit = meta.query_advice(is_access_type_init, Rotation::next());
            let acc_last_write_bit = meta.query_advice(is_access_type_last_write, Rotation::cur());

            // Conditions:
            // 1. Col addr_bit must obey the senmatics of "is next and cur addr equal", that means, if addr_bit == 1, r(cur).addr - r(next).addr == 0
            //    and if addr_bit == 0, r(cur).addr - r(next).addr != 0, more precisely, r(cur).addr - r(next).addr < 0, this part has been checked in the lookup table
            //    By leveaving the inverse of delta_addr, we can make that is_zero_bit == 1 iff delta_addr == 0
            // 2. addresses are different, iff access type of next addr must be init, essentially addr_bit xor acc_init_bit = 1 always holds
            // 3. addresses are different, iff access type of cur addr must be last write, essentially addr_bit xor acc_last_write_bit = 1 always holds
            // Use predicate logic, say A := (addr_bit == 1) B := (acc_last_write_bit == 1), (NOT A -> B) AND  (B -> NOT A)
            // reduces to
            // (A OR B) AND (NOT A OR NOT B) == TRUE
            // (NOT A AND NOT B) OR (A AND B) == FALSE

            vec![
                s.clone() * is_zero_bit.clone() * delta_addr,
                s.clone()
                    * ((one.clone() - is_zero_bit.clone()) * (one.clone() - acc_init_bit.clone())
                        + is_zero_bit.clone() * acc_init_bit.clone()),
                s * ((one.clone() - is_zero_bit.clone())
                    * (one.clone() - acc_last_write_bit.clone())
                    + is_zero_bit * acc_last_write_bit),
            ]
        });

        meta.create_gate("tbl first line check", |meta| {
            // Query selectors
            let init_s = meta.query_selector(init_sel);
            let s = meta.query_selector(sel);

            // Prepare constant
            let one = Expression::Constant(F::ONE);
            // Query init bit
            let init_bit = meta.query_advice(is_access_type_init, Rotation::cur());
            // Query last write bit
            let prev_last_write_bit =
                meta.query_advice(is_access_type_last_write, Rotation::prev());

            // Conditions:
            // 1. init selector is on, acc_init_bit == 1
            // 2. init selector shall be placed on first row,
            //    if this selctor is in the middle, by previous constraints, we immediately know, the address must be different.
            //    By constraint that the different is same (is_zero_bit == 1), that excludes that case where the init selector being
            //    placed in the middle while still passing all the constraints
            vec![
                s.clone() * init_s.clone() * (one.clone() - init_bit),
                s * init_s * prev_last_write_bit,
            ]
        });

        MemTableConfig {
            advice,
            range,
            sel,
            init_sel,
        }
    }

    pub fn assign_range(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let config = &self.config;
        let (binary_range, memory_range, value_range) = if let [binary_range, memory_range, value_range] =
            (0..3)
                .map(|i| config.range[i])
                .collect::<Vec<TableColumn>>()[..]
        {
            (binary_range, memory_range, value_range)
        } else {
            panic!("wrong match")
        };

        let res_binary = layouter.assign_table(
            || "assign binary table",
            |mut table| {
                table.assign_cell(|| "binary range", binary_range, 0, || Value::known(F::ZERO))?;
                table.assign_cell(|| "bianry range", binary_range, 1, || Value::known(F::ONE))?;
                Ok(())
            },
        );

        let mut acc = F::ZERO;
        let res_mem = layouter.assign_table(
            || "assign memory table",
            |mut table| {
                for i in 0..(1 << MEM_RANGE_BITS) {
                    table.assign_cell(|| "memory range", memory_range, i, || Value::known(acc))?;
                    acc += F::ONE;
                }
                Ok(())
            },
        );

        acc = F::ZERO;
        let res_val = layouter.assign_table(
            || "assign value table",
            |mut table| {
                for i in 0..(1 << VALUE_RANGE_BITS) {
                    table.assign_cell(|| "value range", value_range, i, || Value::known(acc))?;
                    acc += F::ONE;
                }
                Ok(())
            },
        );

        // Make sure no res is in error
        let res = [res_binary, res_mem, res_val];
        for res in res.iter() {
            if let Err(_) = res {
                return Err(Error::Synthesis);
            }
        }
        Ok(())
    }

    /// This function will assign the memory table entries
    /// In condition that the entries must be sorted by address and then by id
    pub fn assign_table(
        &self,
        mut layouter: impl Layouter<F>,
        entries: &[MemTableEntry<F>],
    ) -> Result<Vec<MemTableEntry<F>>, Error> {
        let config = &self.config;
        macro_rules! is_not_equal {
            ($lhs:expr, $rhs:expr) => {
                if $lhs != $rhs {
                    Value::known(F::ONE)
                } else {
                    Value::known(F::ZERO)
                }
            };
        }

        let (addr, addr_delta_inv, id, is_access_type_init, is_access_type_last_write, value) =
            if let [addr, addr_delta_inv, id, is_access_type_init, is_access_type_last_write, value] =
                (0..6)
                    .map(|i| config.advice[i])
                    .collect::<Vec<Column<Advice>>>()[..]
            {
                (
                    addr,
                    addr_delta_inv,
                    id,
                    is_access_type_init,
                    is_access_type_last_write,
                    value,
                )
            } else {
                panic!("wrong match")
            };

        // Prepare vec for return
        let mut lw_entries: Vec<MemTableEntry<F>> = vec![];

        // Allocate mem table entries
        // assign_region would be called even in single pass layouter
        // Once for region shape, once for real cells assignment
        let _ = layouter.assign_region(
            || "assign mem table",
            |mut region: Region<F>| {
                let offset = 1;
                // First padding
                if !entries.is_empty() {
                    // Address is not inforced
                    region.assign_advice(|| "padding addr", addr, 0, || Value::known(F::ZERO))?;
                    // The dela is one and invert is one as well
                    region.assign_advice(
                        || "padding addr delta inv",
                        addr_delta_inv,
                        0,
                        || Value::known(F::ZERO),
                    )?;
                    // Id is not enforced
                    region.assign_advice(|| "padding id", id, 0, || Value::known(F::ZERO))?;
                    // Init would be one
                    region.assign_advice(
                        || "padding init",
                        is_access_type_init,
                        0,
                        || Value::known(F::ZERO),
                    )?;
                    // This one is critical, we use this procotol to make sure that the real init
                    region.assign_advice(
                        || "padding last write",
                        is_access_type_last_write,
                        0,
                        || Value::known(F::ZERO),
                    )?;
                    // Value is not enforced
                    region.assign_advice(|| "padding value", value, 0, || Value::known(F::ZERO))?;
                }

                // | addr | is_addr_identical_bit | id | is_access_type_init | is_access_type_last_write | value | sel |
                for (i, entry) in entries.iter().enumerate() {
                    // Selector is enabled for all rows
                    config.sel.enable(&mut region, i + offset)?;
                    // First one, no need for addr_bit
                    if i == 0 {
                        region.assign_advice(
                            || "first addr",
                            addr,
                            i + offset,
                            || Value::known(entry.addr),
                        )?;
                        region.assign_advice(
                            || "first addr_delta_inv",
                            addr_delta_inv,
                            i + offset,
                            || Value::known(F::ZERO),
                        )?; // This one shall not be checked, but cannot be None as well
                        region.assign_advice(
                            || "first id",
                            id,
                            i + offset,
                            || Value::known(entry.id),
                        )?;
                        region.assign_advice(
                            || "first init",
                            is_access_type_init,
                            i + offset,
                            || Value::known(F::ONE),
                        )?;
                        if entries.len() > 1 {
                            region.assign_advice(
                                || "first write be last write",
                                is_access_type_last_write,
                                i + offset,
                                || is_not_equal!(entry.addr, entries[i + 1].addr),
                            )?;

                            if entry.addr != entries[i + 1].addr {
                                // store last write entry
                                lw_entries.push(MemTableEntry {
                                    addr: entry.addr,
                                    id: entry.id,
                                    value: entry.value,
                                });
                            }
                        }
                        region.assign_advice(
                            || "first value",
                            value,
                            i + offset,
                            || Value::known(entry.value),
                        )?;
                        // Enable init selector
                        config.init_sel.enable(&mut region, i + offset)?;
                    }
                    // Last one
                    else if i == entries.len() - 1 {
                        region.assign_advice(
                            || "last addr",
                            addr,
                            i + offset,
                            || Value::known(entry.addr),
                        )?;
                        if entries.len() > 1 {
                            region.assign_advice(
                                || "last addr_delta_inv",
                                addr_delta_inv,
                                i + offset,
                                || {
                                    Value::known(
                                        (entry.addr - entries[i - 1].addr)
                                            .invert()
                                            .unwrap_or(F::ZERO),
                                    )
                                },
                            )?;
                        }
                        region.assign_advice(
                            || "last id",
                            id,
                            i + offset,
                            || Value::known(entry.id),
                        )?;
                        region.assign_advice(
                            || "last init",
                            is_access_type_init,
                            i + offset,
                            || is_not_equal!(entry.addr, entries[i - 1].addr),
                        )?;
                        region.assign_advice(
                            || "last write",
                            is_access_type_last_write,
                            i + offset,
                            || Value::known(F::ONE),
                        )?; // Must be last write for sure
                        region.assign_advice(
                            || "last value",
                            value,
                            i + offset,
                            || Value::known(entry.value),
                        )?;
                        // Must be last write entry
                        lw_entries.push(MemTableEntry {
                            addr: entry.addr,
                            id: entry.id,
                            value: entry.value,
                        });
                    }
                    // Other rows
                    else {
                        region.assign_advice(
                            || format!("{} addr", i),
                            addr,
                            i + offset,
                            || Value::known(entry.addr),
                        )?;
                        region.assign_advice(
                            || format!("{} addr_delta_inv", i),
                            addr_delta_inv,
                            i + offset,
                            || {
                                Value::known(
                                    (entry.addr - entries[i - 1].addr)
                                        .invert()
                                        .unwrap_or(F::ZERO),
                                )
                            },
                        )?;
                        region.assign_advice(
                            || format!("{} id", i),
                            id,
                            i + offset,
                            || Value::known(entry.id),
                        )?;
                        region.assign_advice(
                            || format!("{} init", i),
                            is_access_type_init,
                            i + offset,
                            || is_not_equal!(entry.addr, entries[i - 1].addr),
                        )?;
                        region.assign_advice(
                            || format!("{} write", i),
                            is_access_type_last_write,
                            i + offset,
                            || is_not_equal!(entry.addr, entries[i + 1].addr),
                        )?;
                        region.assign_advice(
                            || format!("{} value", i),
                            value,
                            i + offset,
                            || Value::known(entry.value),
                        )?;
                        // If it is last write, store it
                        if entry.addr != entries[i + 1].addr {
                            lw_entries.push(MemTableEntry {
                                addr: entry.addr,
                                id: entry.id,
                                value: entry.value,
                            });
                        }
                    }
                }
                // Padding last one
                if !entries.is_empty() {
                    // Address is always ascending
                    // Right now we only need to keep that constraint holds
                    // But we can reserve a special value later
                    region.assign_advice(
                        || "padding addr",
                        addr,
                        entries.len() + offset,
                        || Value::known(entries[entries.len() - 1].addr + F::ONE),
                    )?;
                    // The dela is one and invert is one as well
                    region.assign_advice(
                        || "padding addr delta inv",
                        addr_delta_inv,
                        entries.len() + offset,
                        || Value::known(F::ONE),
                    )?;
                    // Id is not enforced
                    region.assign_advice(
                        || "padding id",
                        id,
                        entries.len() + offset,
                        || Value::known(F::ZERO),
                    )?;
                    // Init would be one
                    region.assign_advice(
                        || "padding init",
                        is_access_type_init,
                        entries.len() + offset,
                        || Value::known(F::ONE),
                    )?;
                    // Is last write
                    region.assign_advice(
                        || "padding last write",
                        is_access_type_last_write,
                        entries.len() + offset,
                        || Value::known(F::ONE),
                    )?;
                    // Value is not enforced
                    region.assign_advice(
                        || "padding value",
                        value,
                        entries.len() + offset,
                        || Value::known(F::ZERO),
                    )?;
                }
                Ok(())
            },
        )?;

        // We know lw_entries went twice
        assert!(lw_entries.len() % 2 == 0);
        lw_entries.truncate(lw_entries.len() / 2);

        Ok(lw_entries)
    }
}

#[derive(Clone, Debug)]
pub struct MemTableEntry<F: Field> {
    pub addr: F,
    pub id: F,
    pub value: F,
}

#[derive(Clone, Debug)]
pub struct MemTableEntryCell<F: Field> {
    pub addr: AssignedCell<F, F>,
    pub id: AssignedCell<F, F>,
    pub value: AssignedCell<F, F>,
}

#[cfg(test)]
mod tests {

    use super::*;
    use halo2_proofs::circuit::SimpleFloorPlanner;
    use halo2_proofs::plonk::Circuit;
    use proptest::prelude::Rng;
    #[derive(Clone, Debug)]
    struct CircuitConfig {
        memtbl_config: MemTableConfig,
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

            let memtbl_config = MemTableChip::configure(meta, memtbl_advice, range, memtbl_sel);

            CircuitConfig { memtbl_config }
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
            let _ = memtbl_chip
                .assign_table(layouter.namespace(|| "assign table"), &self.entries)
                .unwrap();
            Ok(())
        }
    }

    #[test]
    fn memtbl_test() {
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

        println!("Sorted Entries are: ");
        for entry in entries.iter() {
            println!(
                "addr: {:?}, id: {:?}, value: {:?}",
                entry.addr, entry.id, entry.value
            );
        }
        println!("End of sorted entries");

        // Create the circuit
        let circuit = MinimalMemTable { entries };

        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        assert_eq!(prover.verify(), Ok(()));
    }
}
