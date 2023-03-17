use group::prime::PrimeGroup;
use maingate::halo2::arithmetic::FieldExt;
use maingate::halo2::dev::CircuitCost;
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
    for (region, value) in cost.regions {
        println!("  {}: {}", region, value);
    }

    //    println!("{:?}", cost.marginal_proof_size());
    //
    //    //println!("min rows: {}", circuit.minimum_rows());
    //    let dimension = DimensionMeasurement::measure(circuit).unwrap();
    //    println!("{:?}", dimension);
}
