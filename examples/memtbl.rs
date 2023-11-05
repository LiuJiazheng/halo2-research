use halo2_proofs::{
    circuit::{Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{
        Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector,
        TableColumn,
    },
    poly::Rotation,
};
use halo2curves::bn256::Fr;
use proptest::prelude::Rng;

const MEM_RANGE_BITS: usize = 4;
const VALUE_RANHE_BITS: usize = 4;

#[derive(Clone, Copy)]
struct MemTableConfig {
    addr: Column<Advice>,
    is_addr_identical_bit: Column<Advice>,
    id: Column<Advice>,
    is_access_type_init: Column<Advice>,
    is_access_type_last_write: Column<Advice>,
    value: Column<Advice>,
    binary_range: TableColumn,
    memory_range: TableColumn,
    value_range: TableColumn,
    sel: Selector,
}

impl MemTableConfig {

    /// In MemTableConfig, we will constrain the following:
    /// r(cur).address == r(next).address => r(cur).id <= r(next).id
    /// r(cur).address != r(next).address <=> r(cur).access_type == last_write
    /// r(cur).address != r(next).address <=> r(next).access_type == init
    /// r(cur).address != r(next).address <=> r(cur).address < r(next).address
    /// Semenatically, it is a sort table, primary key is address, secondary key is id
    /// When address is different, last entry from previous group of address must be last write, and first enrty of next group of address must be init
    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self {
        let [addr, is_addr_identical_bit, id, is_access_type_init, is_access_type_last_write, value] =
            [(); 6].map(|_| meta.advice_column());
        let [binary_range, memory_range, value_range] = [(); 3].map(|_| meta.lookup_table_column());
        let sel = meta.complex_selector();

        // Lookup Conditions:
        // 1. Col addr_bit must be {0,1}
        // 2. Col acc_init_bit must be {0,1}
        // 3. Col acc_last_write_bit must be {0,1}
        // 4. id must be in memory range (for now)
        // 5. value must be in value range
        // 6. addr must be in memory range
        // 7. If addr_bit == 1, r(cur).id <= r(next).id
        // 8. If addr_bit == 0, r(cur).addr < r(next).addr
        // Cannot do a federal query since the tuple (a,b,c...) is not in the lookup table (bianry_range, binary_range, memorary_range...)
        // Each one should be a separate query

        meta.lookup("memory tabel range check 1: addr_bit must be {0,1}", |meta| {
            let s = meta.query_selector(sel);
            let addr_bit = meta.query_advice(is_addr_identical_bit, Rotation::next());

            vec![
                (s * addr_bit.clone(), binary_range),
            ]
        });

        meta.lookup("memory tabel range check 2: acc_init_bit must be {0,1}", |meta| {
            let s = meta.query_selector(sel);
            let acc_init_bit = meta.query_advice(is_access_type_init, Rotation::next());

            vec![
                (s * acc_init_bit, binary_range),
            ]
        });

        meta.lookup("memory tabel range check 3: acc_last_write_bit must be {0,1}", |meta| {
            let s = meta.query_selector(sel);
            let acc_last_write_bit = meta.query_advice(is_access_type_last_write, Rotation::cur());

            vec![
                (s * acc_last_write_bit, binary_range),
            ]
        });

        meta.lookup("memory table range check 4: id must be in memory range", |meta| {
            let s = meta.query_selector(sel);
            let cur_id = meta.query_advice(id, Rotation::cur());

            vec![
                (s * cur_id, memory_range),
            ]
        });

        meta.lookup("memory table range check 5: value must be in value range", |meta| {
            let s = meta.query_selector(sel);
            let value = meta.query_advice(value, Rotation::cur());

            vec![
                (s * value, value_range),
            ]
        });

        meta.lookup("memory table range check 6: addr must be in memory range", |meta| {
            let s = meta.query_selector(sel);
            let cur_addr = meta.query_advice(addr, Rotation::cur());

            vec![
                (s * cur_addr, memory_range),
            ]
        });

        meta.lookup("memory table range check 7: same address, id check", |meta| {
            // Query selector
            let s = meta.query_selector(sel);
            // Get the detla of id
            let cur_id = meta.query_advice(id, Rotation::cur());
            let next_id = meta.query_advice(id, Rotation::next());
            let delta_id = next_id - cur_id.clone();
            // Query bits
            let addr_bit = meta.query_advice(is_addr_identical_bit, Rotation::next());

            vec![
                (s * addr_bit.clone() * delta_id, memory_range),
                //(s * (one.clone() - addr_bit) * (delta_addr - one), memory_range),
            ]
        });

        meta.lookup("memory table range check 8: different address, address stricly ascent", |meta| {
            // Query selector
            let s = meta.query_selector(sel);
            // Get the delta between the current address and the next address
            let cur_addr = meta.query_advice(addr, Rotation::cur());
            let next_addr = meta.query_advice(addr, Rotation::next());
            let delta_addr = next_addr - cur_addr.clone();
            // Query bits
            let addr_bit = meta.query_advice(is_addr_identical_bit, Rotation::next());
            // Prepare constant
            let one = Expression::Constant(Fr::one());

            vec![
                (s * (one.clone() - addr_bit) * (delta_addr - one), memory_range),
            ]
        });

        meta.create_gate("memory table gate constraint", |meta| {
            let s = meta.query_selector(sel);
            // Get the delta between the current address and the next address
            let cur_addr = meta.query_advice(addr, Rotation::cur());
            let next_addr = meta.query_advice(addr, Rotation::next());
            let delta_addr = next_addr - cur_addr;

            // Query bits
            let addr_bit = meta.query_advice(is_addr_identical_bit, Rotation::next());
            let acc_init_bit = meta.query_advice(is_access_type_init, Rotation::next());
            let acc_last_write_bit = meta.query_advice(is_access_type_last_write, Rotation::cur());
            let one = Expression::Constant(Fr::one());

            // Conditions:
            // 1. Col addr_bit must obey the senmatics of "is next and cur addr equal", that means, if addr_bit == 1, r(cur).addr - r(next).addr == 0
            //    and if addr_bit == 0, r(cur).addr - r(next).addr != 0, more precisely, r(cur).addr - r(next).addr < 0, this part has been checked in the lookup table
            // 2. addresses are different, iff access type of next addr must be init, essentially addr_bit xor acc_init_bit = 1 always holds
            // 3. addresses are different, iff access type of cur addr must be last write, essentially addr_bit xor acc_last_write_bit = 1 always holds
            // Use predicate logic, say A := (addr_bit == 1) B := (acc_last_write_bit == 1), (NOT A -> B) AND  (B -> NOT A) 
            // reduces to
            // (A OR B) AND (NOT A OR NOT B) == TRUE
            // (NOT A AND NOT B) OR (A AND B) == FALSE

            vec![
                s.clone() * addr_bit.clone() * delta_addr,
                s.clone() * ((one.clone() - addr_bit.clone()) * (one.clone() - acc_init_bit.clone()) + addr_bit.clone() * acc_init_bit.clone()),
                s * ((one.clone() - addr_bit.clone()) * (one - acc_last_write_bit.clone()) + addr_bit * acc_last_write_bit),
            ]
        });

        Self {
            addr,
            is_addr_identical_bit,
            id,
            is_access_type_init,
            is_access_type_last_write,
            value,
            binary_range,
            memory_range,
            value_range,
            sel,
        }
    }
}

#[derive(Clone, Default)]
struct MemTableEntry {
    addr: Fr,
    id: Fr,
    value: Fr,
}

#[derive(Clone, Default)]
struct MinimalMemTable {
    entries: Vec<MemTableEntry>,
}

impl Circuit<Fr> for MinimalMemTable {
    type Config = MemTableConfig;
    type FloorPlanner = SimpleFloorPlanner;
    #[cfg(feature = "circuit-params")]
    type Params = ();

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        MemTableConfig::configure(meta)
    }

    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<Fr>) -> Result<(), Error> {
        // Allocate the table
        let _= layouter.assign_table(||"assign binary table", |mut table| {
            table.assign_cell(||"binary range", config.binary_range, 0, || Value::known(Fr::zero()))?;
            table.assign_cell(||"bianry range", config.binary_range, 1, || Value::known(Fr::one()))?;
            Ok(())
        });

        let _ = layouter.assign_table(||"assign memory table", |mut table| {
            for i in 0..(1 << MEM_RANGE_BITS) {
                table.assign_cell(||"memory range", config.memory_range, i, || Value::known(Fr::from(i as u64)))?;
            }
            Ok(())
        });

        let _ = layouter.assign_table(||"assign value table", |mut table| {
            for i in 0..(1 << VALUE_RANHE_BITS) {
                table.assign_cell(||"value range", config.value_range, i, || Value::known(Fr::from(i as u64)))?;
            }
            Ok(())
        });

        // Sort entries by address and then by id
        let mut entries = self.entries.clone();
        entries.sort_by(|a, b| {
            if a.addr == b.addr {
                a.id.cmp(&b.id)
            } else {
                a.addr.cmp(&b.addr)
            }
        });

        const ONE: Value<halo2curves::bn256::Fr> = Value::known(Fr::one());
        const ZERO: Value<halo2curves::bn256::Fr> = Value::known(Fr::zero());
        macro_rules! is_equal {
            ($lhs:expr, $rhs:expr) => {
                if $lhs == $rhs {ONE} else {ZERO}
            };
        }
        macro_rules! is_not_equal {
            ($lhs:expr, $rhs:expr) => {
                if $lhs != $rhs {ONE} else {ZERO}
            };
        }
        // Allocate mem table entries
        layouter.assign_region(||"assign mem table", |mut region: Region<Fr>| {
            // | addr | is_addr_identical_bit | id | is_access_type_init | is_access_type_last_write | value | sel |
            for (i, entry) in entries.iter().enumerate() {
                // First one, no need for addr_bit
                if i == 0 {
                    region.assign_advice(||"first addr", config.addr, i, || Value::known(entry.addr))?;
                    region.assign_advice(||"first id", config.id, i, || Value::known(entry.id))?;
                    region.assign_advice(||"first init", config.is_access_type_init, i, || ONE)?;
                    if entries.len() > 1 {
                        region.assign_advice(||"first write be last write", config.is_access_type_last_write, i, || is_not_equal!(entry.addr, entries[i+1].addr))?;
                    }
                    region.assign_advice(||"first value", config.value, i, || Value::known(entry.value))?;
                    config.sel.enable(&mut region, i)?;
                }
                // Last one, no need for sel
                else if i == entries.len() - 1 {
                    region.assign_advice(||"last addr", config.addr, i, || Value::known(entry.addr))?;
                    region.assign_advice(||"last addr_bit", config.is_addr_identical_bit, i, || is_equal!(entry.addr, entries[i-1].addr))?;
                    region.assign_advice(||"last id", config.id, i, || Value::known(entry.id))?;
                    region.assign_advice(||"last init", config.is_access_type_init, i, || is_not_equal!(entry.addr, entries[i-1].addr))?;
                    region.assign_advice(||"last write", config.is_access_type_last_write, i, || ONE)?; // Must be last write for sure
                    region.assign_advice(||"last value", config.value, i, || Value::known(entry.value))?;
                }
                // Other rows
                else {
                    region.assign_advice(||format!("{} addr", i), config.addr, i, || Value::known(entry.addr))?;
                    region.assign_advice(||format!("{} addr_bit", i), config.is_addr_identical_bit, i, || is_equal!(entry.addr, entries[i-1].addr))?;
                    region.assign_advice(||format!("{} id", i), config.id, i, || Value::known(entry.id))?;
                    region.assign_advice(||format!("{} init", i), config.is_access_type_init, i, || is_not_equal!(entry.addr, entries[i-1].addr))?;
                    region.assign_advice(||format!("{} write", i), config.is_access_type_last_write, i, || is_not_equal!(entry.addr, entries[i+1].addr))?;
                    region.assign_advice(||format!("{} value", i), config.value, i, || Value::known(entry.value))?;
                    config.sel.enable(&mut region, i)?;
                }
            }
            Ok(())
        })

    }
}

fn main() {
    use std::{
        fs::File,
        io::{BufReader, BufWriter, Write},
    };

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
    use halo2curves::bn256::{Bn256, G1Affine};
    use halo2_proofs::dev::MockProver;
    use rand_core::OsRng;

    // ANCHOR: test-circuit
    // The number of rows in our circuit cannot exceed 2^k. Since our example
    // circuit is very small, we can pick a very small value here.
    let k = 8;

    // Create an buffer
    let mut entries: Vec<MemTableEntry> = vec![];

    // Prepare the private inputs to the circuit!
    let mut rng = OsRng;
    for id in 0..(1<<MEM_RANGE_BITS) {
        // we only genegate 6 addresses, by Pigeonhole principle there must be some address with more than one entry
        let addr = Fr::from(rng.gen_range(0..6) as u64);
        let value = Fr::from(rng.gen_range(0..(1 << VALUE_RANHE_BITS)) as u64);
        entries.push(MemTableEntry { addr, id: Fr::from(id as u64), value });
    }

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
    let pk = ProvingKey::<G1Affine>::read::<_, MinimalMemTable>(
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
    >(
        &params,
        &pk,
        &[circuit],
        &[&[]],
        OsRng,
        &mut transcript,
    )
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
    >(
        &params,
        pk.get_vk(),
        strategy,
        &[&[]],
        &mut transcript
    )
    .is_ok());

    println!("Proof and verification succeeded!");
}
