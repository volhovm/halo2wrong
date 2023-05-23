use std::{
    cmp, fmt, iter,
    num::ParseIntError,
    str::FromStr,
    time::{Duration, Instant},
};

use group::ff::Field;
use group::prime::PrimeGroup;
use group::{Curve, Group};
use maingate::halo2::arithmetic::{best_multiexp, FieldExt};
use maingate::halo2::dev::CircuitCost;
use maingate::halo2::halo2curves::pasta::pallas;
use maingate::halo2::halo2curves::pasta::Fp as PastaFp;
use maingate::halo2::plonk::Circuit;

pub struct Estimator {
    /// Scalars for estimating multiexp performance.
    multiexp_scalars: Vec<pallas::Scalar>,
    /// Bases for estimating multiexp performance.
    multiexp_bases: Vec<pallas::Affine>,
}

impl fmt::Debug for Estimator {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Estimator")
    }
}

impl Estimator {
    pub fn random(k: usize) -> Self {
        let max_size = 1 << (k + 1);
        //let max_size = 1 << k;
        let mut rng = rand_core::OsRng;

        println!("Generating {} points for the estimator", 2 * max_size);

        let thread1 = std::thread::spawn(move || {
            (0..max_size)
                .map(|_| pallas::Scalar::random(&mut rng))
                .collect()
        });

        let thread2 = std::thread::spawn(move || {
            (0..max_size)
                .map(|_| pallas::Point::random(&mut rng).to_affine())
                .collect()
        });

        let multiexp_scalars = thread1.join().unwrap();
        let multiexp_bases = thread2.join().unwrap();

        Estimator {
            multiexp_scalars,
            multiexp_bases,
        }
    }

    pub fn multiexp(&self, size: usize) -> Duration {
        println!("Estimating {} multiexps...", size);
        let start = Instant::now();
        best_multiexp(&self.multiexp_scalars[..size], &self.multiexp_bases[..size]);
        Instant::now().duration_since(start)
    }
}

pub fn simple_msm_estimator() {
    use maingate::halo2::multicore::ThreadPoolBuilder;

    let threads = 1;
    let k = 15;

    ThreadPoolBuilder::new()
        .num_threads(threads)
        .build_global()
        .unwrap();
    let e = &Estimator::random(k as usize);
    let duration = e.multiexp(1 << k);
    println!(
        "Running 2^{} multiexp with {} threads takes {:?}",
        k, threads, duration
    );
}

/// Prints human-readable evaluation of circuit size and cost.
pub fn measure_circuit_size<G: PrimeGroup, C: Circuit<G::Scalar> + std::fmt::Debug>(
    circuit: &C,
    k: u32,
    estimator: &Estimator,
) where
    G::Scalar: FieldExt,
{
    //println!("{:?}", circuit);
    println!("{}", std::any::type_name::<C>());
    let cost: CircuitCost<_, _> = CircuitCost::<G, C>::measure(k, circuit);
    for (region, value) in &cost.regions {
        println!("  {}: {}", region, value);
    }
    println!("Cost: {:?}", &cost);
    println!(
        "Verification time: {:?}",
        measure_verification_time(&cost, estimator)
    );

    let proof_size = cost.proof_size(1);
    println!("Proof size: {:?}", proof_size);

    //    verifier_group.bench_with_input(
    //        BenchmarkId::from_parameter(k),
    //        &(&params, pk.get_vk(), &proof[..]),
    //        |b, &(params, vk, proof)| {
    //            b.iter(|| verifier(params, vk, proof));
    //        },
    //    );

    //    println!("{:?}", cost.marginal_proof_size());
    //
    //    //println!("min rows: {}", circuit.minimum_rows());
    //    let dimension = DimensionMeasurement::measure(circuit).unwrap();
    //    println!("{:?}", dimension);
}

pub fn measure_circuit_real<C: Circuit<PastaFp> + std::fmt::Debug>(circuit: C, k: u32) {
    use maingate::halo2::circuit::{Cell, Layouter, SimpleFloorPlanner, Value};
    use maingate::halo2::halo2curves::pasta::{EqAffine, Fp};
    use maingate::halo2::multicore::ThreadPoolBuilder;
    use maingate::halo2::plonk::*;
    use maingate::halo2::poly::{commitment::ParamsProver, Rotation};
    use maingate::halo2::transcript::{Blake2bRead, Blake2bWrite, Challenge255};
    use maingate::halo2::SerdeFormat;
    use maingate::halo2::{
        poly::{
            ipa::{
                commitment::{IPACommitmentScheme, ParamsIPA},
                multiopen::ProverIPA,
                strategy::SingleStrategy,
            },
            VerificationStrategy,
        },
        transcript::{TranscriptReadBuffer, TranscriptWriterBuffer},
    };
    use rand_core::OsRng;
    use std::fs::File;
    use std::path::Path;
    use std::time::{SystemTime, UNIX_EPOCH};

    let t_1 = SystemTime::now();

    let params: ParamsIPA<EqAffine> = ParamsIPA::new(k);
    let circuit_empty = circuit.without_witnesses();
    println!("generating keys");
    //let (vk, pk) = if !Path::new("plonk_vk.raw").exists() {
    //    let vk_file = File::create("plonk_vk.raw").unwrap();
    //    let pk_file = File::create("plonk_pk.raw").unwrap();
    //    let vk = keygen_vk(&params, &circuit_empty).expect("keygen_vk should not
    // fail");    let pk = keygen_pk(&params, vk,
    // &circuit_empty).expect("keygen_pk should not fail");
    //    vk.write(SerdeFormat::Processed);
    //    pk.write(SerdeFormat::Processed);
    //    (vk, pk)
    //} else {
    //    let mut vk_file = File::open("plonk_vk.raw").unwrap();
    //    let vk = VerifyingKey::read(&mut vk_file, SerdeFormat::Processed);
    //    let mut pk_file = File::open("plonk_pk.raw").unwrap();
    //    let pk = ProvingKey::read(&mut pk_file, SerdeFormat::Processed);
    //    (vk, pk)
    //};
    let vk = keygen_vk(&params, &circuit_empty).expect("keygen_vk should not fail");
    let pk = keygen_pk(&params, vk, &circuit_empty).expect("keygen_pk should not fail");

    let t_2 = SystemTime::now();

    //ThreadPoolBuilder::new()
    //    .num_threads(1)
    //    .build_global()
    //    .unwrap();

    println!("generating proof");
    let mut transcript = Blake2bWrite::<_, _, Challenge255<EqAffine>>::init(vec![]);
    create_proof::<IPACommitmentScheme<EqAffine>, ProverIPA<EqAffine>, _, _, _, _>(
        &params,
        &pk,
        &[circuit],
        &[&[&[]]],
        OsRng,
        &mut transcript,
    )
    .expect("proof generation should not fail");
    let proof = transcript.finalize();

    let t_3 = SystemTime::now();

    println!("verifying proof");
    let strategy = SingleStrategy::new(&params);
    let mut transcript = Blake2bRead::<_, _, Challenge255<_>>::init(&proof[..]);
    let res = verify_proof(&params, pk.get_vk(), strategy, &[&[&[]]], &mut transcript).is_ok();

    let t_4 = SystemTime::now();

    println!("verification res: {}", res);

    let t_delta1 = t_2.duration_since(t_1).unwrap();
    let t_delta2 = t_3.duration_since(t_2).unwrap();
    let t_delta3 = t_4.duration_since(t_3).unwrap();
    let t_total = t_4.duration_since(t_1).unwrap();

    println!(
        "Circuit time (total {:?}):
  keygen    {:?}
  prove     {:?}
  verify    {:?}",
        t_total, t_delta1, t_delta2, t_delta3
    );
}

pub fn measure_proof_size<G: PrimeGroup, C: Circuit<G::Scalar>>(cost: &CircuitCost<G, C>) -> usize {
    let size = |points: usize, scalars: usize| points * 32 + scalars * 32;

    // PLONK:
    // - 32 bytes (commitment) per advice column
    // - 3 * 32 bytes (commitments) + 5 * 32 bytes (evals) per lookup argument
    // - 32 bytes (commitment) + 2 * 32 bytes (evals) per permutation argument
    // - 32 bytes (eval) per column per permutation argument
    let plonk = size(1, 0) * cost.advice_columns
        + size(3, 5) * cost.lookups
        + size(1, 2 + cost.permutation_cols as usize);

    // @volhovm: FIXME check the above is right
    //        + cost
    //            .permutations
    //            .iter()
    //            .map(|p| size(1, 2 + p.columns))
    //            .sum::<usize>();

    // Vanishing argument:
    // - (max_deg - 1) * 32 bytes (commitments) + (max_deg - 1) * 32 bytes (h_evals)
    //   for quotient polynomial
    // - 32 bytes (eval) per column query
    let vanishing = size(cost.max_deg - 1, cost.max_deg - 1) + size(0, cost.column_queries_num);

    // Multiopening argument:
    // - f_commitment (32 bytes)
    // - 32 bytes (evals) per set of points in multiopen argument
    let multiopen = size(1, cost.point_sets);

    // Polycommit:
    // - s_poly commitment (32 bytes)
    // - inner product argument (k rounds * 2 * 32 bytes)
    // - a (32 bytes)
    // - xi (32 bytes)
    let polycomm = size(1 + 2 * cost.k as usize, 2);

    plonk + vanishing + multiopen + polycomm
}

fn measure_verification_time<G: PrimeGroup, C: Circuit<G::Scalar>>(
    cost: &CircuitCost<G, C>,
    estimator: &Estimator,
) -> Duration {
    println!("estimating verificaiton time...");
    // TODO: Estimate cost of BLAKE2b.

    // TODO: This isn't accurate; most of these will have zero scalars.
    let g_scalars = 1 << cost.k;

    // - f_commitment
    // - q_commitments
    let multiopen = 1 + cost.column_queries_num;

    // - \iota
    // - Rounds
    // - H
    // - U
    let polycomm = 1 + (2 * cost.k) + 1 + 1;

    estimator.multiexp((g_scalars + multiopen + (polycomm as usize)) as usize)
}
