use core::panic;
use halo2_proofs::{
    arithmetic::Field,
    circuit::{Chip, Layouter, Region, SimpleFloorPlanner, Value, AssignedCell},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Selector, TableColumn},
    poly::Rotation,
};
use proptest::prelude::Rng;
use std::marker::PhantomData;

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
