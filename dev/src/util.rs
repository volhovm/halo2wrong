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
use maingate::halo2::plonk::Circuit;

/// Prints human-readable evaluation of circuit size and cost.
pub fn measure_circuit_size<G: PrimeGroup, C: Circuit<G::Scalar> + std::fmt::Debug>(
    circuit: &C,
    k: u32,
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
    println!("Verification time: {:?}", measure_verification_time(&cost));

    let proof_size = cost.proof_size(1);
    println!("Proof size: {:?}", proof_size);

    //    println!("{:?}", cost.marginal_proof_size());
    //
    //    //println!("min rows: {}", circuit.minimum_rows());
    //    let dimension = DimensionMeasurement::measure(circuit).unwrap();
    //    println!("{:?}", dimension);
}

struct Estimator {
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
    fn random(k: usize) -> Self {
        let max_size = 1 << (k + 1);
        let mut rng = rand_core::OsRng;

        Estimator {
            multiexp_scalars: (0..max_size)
                .map(|_| pallas::Scalar::random(&mut rng))
                .collect(),
            multiexp_bases: (0..max_size)
                .map(|_| pallas::Point::random(&mut rng).to_affine())
                .collect(),
        }
    }

    fn multiexp(&self, size: usize) -> Duration {
        let start = Instant::now();
        best_multiexp(&self.multiexp_scalars[..size], &self.multiexp_bases[..size]);
        Instant::now().duration_since(start)
    }
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

    let estimator = Estimator::random(cost.k as usize);
    estimator.multiexp((g_scalars + multiopen + (polycomm as usize)) as usize)
}
