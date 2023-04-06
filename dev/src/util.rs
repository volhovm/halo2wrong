use std::{
    cmp, fmt, iter,
    num::ParseIntError,
    str::FromStr,
    time::{Duration, Instant},
};

use group::prime::PrimeGroup;
use maingate::halo2::arithmetic::FieldExt;
use maingate::halo2::dev::CircuitCost;
use maingate::halo2::plonk::Circuit;

pub fn halo2_proof_size<G: PrimeGroup, C: Circuit<G::Scalar> + std::fmt::Debug>(
    ccost: &CircuitCost<G, C>,
) -> usize
where
    G::Scalar: FieldExt,
{
    let size = |points: usize, scalars: usize| points * 32 + scalars * 32;

    // PLONK:
    // - 32 bytes (commitment) per advice column
    // - 3 * 32 bytes (commitments) + 5 * 32 bytes (evals) per lookup argument
    // - 32 bytes (commitment) + 2 * 32 bytes (evals) per permutation argument
    // - 32 bytes (eval) per column per permutation argument
    let plonk = size(1, 0) * ccost.advice_columns
        + size(3, 5) * ccost.lookups
        + size(1, 2 + ccost.permutation_cols);

    // Vanishing argument:
    // - (max_deg - 1) * 32 bytes (commitments) + (max_deg - 1) * 32 bytes (h_evals)
    //   for quotient polynomial
    // - 32 bytes (eval) per column query
    let vanishing = size(ccost.max_deg - 1, ccost.max_deg - 1) + size(0, ccost.column_queries);

    // Multiopening argument:
    // - f_commitment (32 bytes)
    // - 32 bytes (evals) per set of points in multiopen argument
    let multiopen = size(1, ccost.point_sets);

    // Polycommit:
    // - s_poly commitment (32 bytes)
    // - inner product argument (k rounds * 2 * 32 bytes)
    // - a (32 bytes)
    // - xi (32 bytes)
    let polycomm = size(1 + 2 * ccost.k, 2);

    plonk + vanishing + multiopen + polycomm
}

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

    let proof_size = cost.proof_size(1);
    println!("Proof size: {:?}", proof_size);

    //    println!("{:?}", cost.marginal_proof_size());
    //
    //    //println!("min rows: {}", circuit.minimum_rows());
    //    let dimension = DimensionMeasurement::measure(circuit).unwrap();
    //    println!("{:?}", dimension);
}
