use core::panic;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Chip, Layouter, Region, SimpleFloorPlanner, Value, AssignedCell},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use proptest::prelude::Rng;
use std::marker::PhantomData;

const MEM_RANGE_BITS: usize = 4;
const VALUE_RANGE_BITS: usize = 4;

struct MemTableChip<F: Field> {
    config: MemTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct MemTableConfig {
    // | addr | addr_delta_inv | id | is_access_type_init | is_access_type_last_write | value |
    advice: [Column<Advice>; 6],
    // | binary_range | memory_range | value_range |
    range: [TableColumn; 3],
    // Selector for region
    sel: Selector,
    // Selector for init row
    init_sel: Selector,
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
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
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
    fn configure(
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

    fn assign_range(&self, mut layouter: impl Layouter<F>) -> Result<(), Error> {
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

    fn assign_table(
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

struct LastWriteTableChip<F: Field> {
    config: LastWriteTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct LastWriteTableConfig {
    // | addr | id | value |
    advice: [Column<Advice>; 3],
    // selector for region
    sel: Selector,
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
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    /// Configure the last write table
    /// memtbl_schema: [addr, id, value, is_last_write]
    /// last_write_schema: [addr, id, value, heritage]
    fn configure(
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

    #[allow(unused)]
    fn zero_padding_one_row(
        mut layouter: impl Layouter<F>,
        schema: [Column<Advice>; 3],
        sel: Selector,
    ) -> Result<(), Error> {
        let (addr, id, value) = if let [addr, id, value] =
            (0..3).map(|i| schema[i]).collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        layouter.assign_region(
            || "zero padding one row",
            |mut region: Region<F>| {
                region.assign_advice(|| "addr", addr, 0, || Value::known(F::ZERO))?;
                region.assign_advice(|| "id", id, 0, || Value::known(F::ZERO))?;
                region.assign_advice(|| "value", value, 0, || Value::known(F::ZERO))?;
                sel.enable(&mut region, 0)?;
                Ok(())
            },
        )
    }

    fn assign_lwtbl_from_memtbl(
        &self,
        mut layouter: impl Layouter<F>,
        memtbl_entries: &[MemTableEntry<F>],
    ) -> Result<Vec<MemTableEntryCell<F>>, Error> {
        let config = &self.config;
        let (lw_addr, lw_id, lw_value) = if let [addr, id, value] = (0..3)
            .map(|i| config.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        let mut lw_table: Vec<MemTableEntryCell<F>> = vec![];
        // Allocate lwtbl based on the given entries
        layouter.assign_region(
            || "assign lw table",
            |mut region: Region<F>| {
                for (i, entry) in memtbl_entries.iter().enumerate() {
                    let cell_addr = region.assign_advice(
                        || format!("{} addr", i),
                        lw_addr,
                        i,
                        || Value::known(entry.addr),
                    ).unwrap();
                    let cell_id = region.assign_advice(
                        || format!("{} id", i),
                        lw_id,
                        i,
                        || Value::known(entry.id),
                    ).unwrap();
                    let cell_value = region.assign_advice(
                        || format!("{} value", i),
                        lw_value,
                        i,
                        || Value::known(entry.value),
                    ).unwrap();
                    config.sel.enable(&mut region, i)?;
                    lw_table.push(MemTableEntryCell {
                        addr: cell_addr,
                        id: cell_id,
                        value: cell_value,
                    });
                }
                Ok(())
            },
        );

        // Above assignment would do twice
        assert!(lw_table.len() % 2 == 0);
        lw_table.truncate(lw_table.len() / 2);

        Ok(lw_table)
    }
}

struct ConcatTableChip<F: Field> {
    config: ConcatTableConfig,
    _marker: PhantomData<F>,
}

#[derive(Clone, Debug)]
struct ConcatTableConfig {
    joint_table_config: LastWriteTableConfig,
    left_table_config: LastWriteTableConfig,
    right_table_config: LastWriteTableConfig,
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
    fn construct(config: <Self as Chip<F>>::Config) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    fn configure(
        meta: &mut ConstraintSystem<F>,
        left_table_config: LastWriteTableConfig,
        right_table_config: LastWriteTableConfig,
        joint_table_config: LastWriteTableConfig,
        range_table: [TableColumn;3],
    ) -> <Self as Chip<F>>::Config {
        macro_rules! common_constraint {
            ($config:expr) => {
                // Enforce equality
                for col in $config.advice.iter() {
                    meta.enable_equality(*col);
                }

                // Prepare static range table
                let (_, memory_range, value_range) = if let [binary_range, memory_range, value_range] =
                    (0..3)
                        .map(|i| range_table[i])
                        .collect::<Vec<TableColumn>>()[..]
                {
                    (binary_range, memory_range, value_range)
                } else {
                    panic!("wrong match")
                };

                // Prepare columns
                let (addr, id, value) = if let [addr, id, value] = (0..3)
                    .map(|i| $config.advice[i])
                    .collect::<Vec<Column<Advice>>>()[..]
                {
                    (addr, id, value)
                } else {
                    panic!("wrong match")
                };

                // Common constraints
                meta.lookup(format!("{} addr", stringify!($config)), |meta| {
                    let s = meta.query_selector($config.sel);
                    let addr = meta.query_advice(addr, Rotation::cur());

                    vec![(s * addr, memory_range)]
                });

                meta.lookup(format!("{} id", stringify!($config)), |meta| {
                    let s = meta.query_selector($config.sel);
                    let id = meta.query_advice(id, Rotation::cur());

                    vec![(s * id, memory_range)]
                });

                meta.lookup(format!("{} value", stringify!($config)), |meta| {
                    let s = meta.query_selector($config.sel);
                    let value = meta.query_advice(value, Rotation::cur());

                    vec![(s * value, value_range)]
                });

            };
        }
        common_constraint!(left_table_config);
        common_constraint!(right_table_config);
        common_constraint!(joint_table_config);

        // Create selectors within this chip
        let left_sel = meta.complex_selector();
        let right_sel = meta.complex_selector();

        // Joint table constraints
        // For any t \belongs to left table, t \belongs to joint table
        meta.lookup_any("left table belongs to joint table", |meta| {
            let s = meta.query_selector(left_table_config.sel);
            let addr = meta.query_advice(left_table_config.advice[0], Rotation::cur());
            let id = meta.query_advice(left_table_config.advice[1], Rotation::cur());
            let value = meta.query_advice(left_table_config.advice[2], Rotation::cur());

            let joint_addr = meta.query_advice(joint_table_config.advice[0], Rotation::cur());
            let joint_id = meta.query_advice(joint_table_config.advice[1], Rotation::cur());
            let joint_value = meta.query_advice(joint_table_config.advice[2], Rotation::cur());

            vec![
                (s.clone() * addr, joint_addr),
                (s.clone() * id, joint_id),
                (s * value, joint_value),
            ]
        });

        // For any t \belongs to right table, t \belongs to joint table
        meta.lookup_any("right table belongs to joint table", |meta| {
            let s = meta.query_selector(right_table_config.sel);
            let addr = meta.query_advice(right_table_config.advice[0], Rotation::cur());
            let id = meta.query_advice(right_table_config.advice[1], Rotation::cur());
            let value = meta.query_advice(right_table_config.advice[2], Rotation::cur());

            let joint_addr = meta.query_advice(joint_table_config.advice[0], Rotation::cur());
            let joint_id = meta.query_advice(joint_table_config.advice[1], Rotation::cur());
            let joint_value = meta.query_advice(joint_table_config.advice[2], Rotation::cur());

            vec![
                (s.clone() * addr, joint_addr),
                (s.clone() * id, joint_id),
                (s * value, joint_value),
            ]
        });

        // For any t \belong to joint table, t \belongs to left table or t \belongs to right table
        meta.lookup_any("joint table belongs to left table or right table", |meta| {
            let s = meta.query_selector(joint_table_config.sel);
            let addr = meta.query_advice(joint_table_config.advice[0], Rotation::cur());
            let id = meta.query_advice(joint_table_config.advice[1], Rotation::cur());
            let value = meta.query_advice(joint_table_config.advice[2], Rotation::cur());

            let left_addr = meta.query_advice(left_table_config.advice[0], Rotation::cur());
            let left_id = meta.query_advice(left_table_config.advice[1], Rotation::cur());
            let left_value = meta.query_advice(left_table_config.advice[2], Rotation::cur());
            let left_sel = meta.query_selector(left_sel);

            let right_addr = meta.query_advice(right_table_config.advice[0], Rotation::cur());
            let right_id = meta.query_advice(right_table_config.advice[1], Rotation::cur());
            let right_value = meta.query_advice(right_table_config.advice[2], Rotation::cur());
            let right_sel = meta.query_selector(right_sel);

            vec![
                (s.clone()* addr, left_sel.clone()*left_addr + right_sel.clone()*right_addr),
                (s.clone()* id, left_sel.clone()*left_id + right_sel.clone()*right_id),
                (s.clone()* value, left_sel*left_value + right_sel*right_value),
            ]
        });

        // A special constraint, left table and right table shall not overlap
        meta.create_gate("left and right table of joint table shall not overlap", |meta| {
            let left_sel = meta.query_selector(left_sel);
            let right_sel = meta.query_selector(right_sel);

            vec![
                left_sel * right_sel,
            ]
        });

        ConcatTableConfig {
            joint_table_config,
            left_table_config,
            right_table_config,
            left_sel,
            right_sel,
        }
    }

    // Load a last write table unconditionally
    // Ideally we shall use some commitment to check it does from previous segment
    // Here we simplify it a bit
    fn load_lw_table(mut layouter: impl Layouter<F>, table_config: &LastWriteTableConfig, entries: &[MemTableEntry<F>]) -> Vec<MemTableEntryCell<F>> {
        let (addr, id, value) = if let [addr, id, value] = (0..3)
            .map(|i| table_config.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        let mut lw_table: Vec<MemTableEntryCell<F>> = vec![];
        layouter.assign_region(|| "assign a lw table", |mut region: Region<F>| {
            for (i, entry) in entries.iter().enumerate() {
                let cell_addr = region.assign_advice(
                    || format!("{} addr", i),
                    addr,
                    i,
                    || Value::known(entry.addr),
                ).unwrap();
                let cell_id = region.assign_advice(
                    || format!("{} id", i),
                    id,
                    i,
                    || Value::known(entry.id),
                ).unwrap();
                let cell_value = region.assign_advice(
                    || format!("{} value", i),
                    value,
                    i,
                    || Value::known(entry.value),
                ).unwrap();
                table_config.sel.enable(&mut region, i)?;
                lw_table.push(MemTableEntryCell {
                    addr: cell_addr,
                    id: cell_id,
                    value: cell_value,
                });
            }
            Ok(())
        });

        // Above assignment would do twice
        assert!(lw_table.len() % 2 == 0);
        lw_table.truncate(lw_table.len() / 2);

        lw_table
    }

    // Implement concat on witness
    fn concat(&self, mut layouter: impl Layouter<F>, left_table: Vec<MemTableEntryCell<F>>, right_table: Vec<MemTableEntryCell<F>>) -> Result<(), Error> {
        let config = &self.config;
        let (left_addr, left_id, left_value) = if let [addr, id, value] = (0..3)
            .map(|i| config.left_table_config.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        let (right_addr, right_id, right_value) = if let [addr, id, value] = (0..3)
            .map(|i| config.right_table_config.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        let (joint_addr, joint_id, joint_value) = if let [addr, id, value] = (0..3)
            .map(|i| config.joint_table_config.advice[i])
            .collect::<Vec<Column<Advice>>>()[..]
        {
            (addr, id, value)
        } else {
            panic!("wrong match")
        };

        let left_sel = config.left_sel;
        let right_sel = config.right_sel;

        // Allocate lwtbl based on the given entries
        layouter.assign_region(
            || "concat lw table",
            |mut region: Region<F>| {
                for (i, entry) in left_table.iter().enumerate() {
                    // Copy left table
                    entry.addr.copy_advice(|| format!("concat on {}", i), &mut region, joint_addr, i)?;
                    entry.id.copy_advice(|| format!("concat on {}", i), &mut region, joint_id, i)?;
                    entry.value.copy_advice(|| format!("concat on {}", i), &mut region, joint_value, i)?;
                    left_sel.enable(&mut region, i);
                }
                let offset = left_table.len();
                for (i, entry) in right_table.iter().enumerate() {
                    // Copy right table
                    entry.addr.copy_advice(|| format!("concat on {}", i), &mut region, joint_addr, i + offset)?;
                    entry.id.copy_advice(|| format!("concat on {}", i), &mut region, joint_id, i + offset)?;
                    entry.value.copy_advice(|| format!("concat on {}", i), &mut region, joint_value, i + offset)?;
                    right_sel.enable(&mut region, i + offset);
                }
                Ok(())
            },
        )
    }
}

#[derive(Clone, Debug)]
struct MemTableEntry<F: Field> {
    addr: F,
    id: F,
    value: F,
}

#[derive(Clone, Debug)]
struct MemTableEntryCell<F: Field> {
    addr: AssignedCell<F, F>,
    id: AssignedCell<F, F>,
    value: AssignedCell<F, F>,
}

#[derive(Clone, Debug)]
struct CircuitConfig {
    memtbl_config: MemTableConfig,
    lwtbl_config: LastWriteTableConfig,
}

#[derive(Default, Debug)]
struct MinimalMemTable<F: Field> {
    entries: Vec<MemTableEntry<F>>,
    previous_lw_entries: Vec<MemTableEntry<F>>,
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
        let lwtbl_from_memtbl = memtbl_chip
            .assign_table(layouter.namespace(|| "assign table"), &self.entries)
            .unwrap();

        //let mut lwtbl_from_memtbl = lwtbl_from_memtbl[..lwtbl_from_memtbl.len() - 1].to_vec();
        //lwtbl_from_memtbl[0].id = lwtbl_from_memtbl[0].id + F::ONE;;
        println!("Single synthesize: ");
        for entry in lwtbl_from_memtbl.iter() {
            println!(
                "addr: {:?}, id: {:?}, value: {:?}",
                entry.addr, entry.id, entry.value
            );
        }
        println!("End of single synthesize");
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

fn main() {
    use std::{
        fs::File,
        io::{BufReader, BufWriter, Write},
    };

    use halo2_proofs::dev::MockProver;
    use halo2_proofs::{
        plonk::{create_proof, keygen_pk, keygen_vk, verify_proof, ProvingKey},
        poly::kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::SingleStrategy,
        },
        transcript::{
            Blake2bRead, Blake2bWrite, Challenge255, TranscriptReadBuffer, TranscriptWriterBuffer,
        },
        SerdeFormat,
    };
    use halo2curves::bn256::{Bn256, Fr, G1Affine};
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

    let params = ParamsKZG::<Bn256>::setup(k, OsRng);
    let vk = keygen_vk(&params, &circuit).expect("vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit).expect("pk should not fail");

    let f = File::create("serialization-test.pk").unwrap();
    let mut writer = BufWriter::new(f);
    pk.write(&mut writer, SerdeFormat::RawBytes).unwrap();
    writer.flush().unwrap();

    let f = File::open("serialization-test.pk").unwrap();
    let mut reader = BufReader::new(f);
    #[allow(clippy::unit_arg)]
    let pk = ProvingKey::<G1Affine>::read::<_, MinimalMemTable<Fr>>(
        &mut reader,
        SerdeFormat::RawBytes,
        #[cfg(feature = "circuit-params")]
        circuit.params(),
    )
    .unwrap();

    std::fs::remove_file("serialization-test.pk").unwrap();

    let mut transcript = Blake2bWrite::<_, _, Challenge255<_>>::init(vec![]);
    create_proof::<
        KZGCommitmentScheme<Bn256>,
        ProverGWC<'_, Bn256>,
        Challenge255<G1Affine>,
        _,
        Blake2bWrite<Vec<u8>, G1Affine, Challenge255<_>>,
        _,
    >(&params, &pk, &[circuit], &[&[]], OsRng, &mut transcript)
    .expect("prover should not fail");
    let proof = transcript.finalize();

    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    assert!(verify_proof::<
        KZGCommitmentScheme<Bn256>,
        VerifierGWC<'_, Bn256>,
        Challenge255<G1Affine>,
        Blake2bRead<&[u8], G1Affine, Challenge255<G1Affine>>,
        SingleStrategy<'_, Bn256>,
    >(&params, pk.get_vk(), strategy, &[&[]], &mut transcript)
    .is_ok());

    println!("Proof and verification succeed!");
}
