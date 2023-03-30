use group::ff::Field;
use group::prime::PrimeGroup;
use group::{Curve, Group};

use halo2_proofs::arithmetic::{CurveAffine, FieldExt};
use halo2_proofs::circuit::{AssignedCell, Cell, Layouter, Region, SimpleFloorPlanner};
use halo2_proofs::pairing::bls12_381::{G1Affine, G1};
use halo2_proofs::pairing::bn256::{Fr, G1Affine as BN256_G1Affine, G1 as BN256_G1};
use halo2_proofs::pairing::group::prime::PrimeCurveAffine;
use halo2_proofs::plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Fixed, Selector};
use halo2_proofs_junyu as halo2_proofs;

use rand_core::OsRng;
use std::cell::RefCell;
use std::marker::PhantomData;
use std::rc::Rc;

//use halo2::{
//    arithmetic::{BaseExt},
//    circuit::{Layouter, SimpleFloorPlanner},
//    dev::MockProver,
//    pairing::bn256::{Bn256, Fr, G1Affine},
//    plonk::{
//        create_proof, keygen_pk, keygen_vk, verify_proof, Circuit,
// ConstraintSystem, Error,        SingleVerifier,
//    },
//    poly::commitment::{Params, ParamsVerifier},
//    transcript::{Blake2bRead, Blake2bWrite, Challenge255},
//};
//use rand::{rngs::OsRng, SeedableRng};
//use rand_xorshift::XorShiftRng;

use halo2ecc_s::assign::AssignedPoint;
use halo2ecc_s::circuit::base_chip::{BaseChip, BaseChipConfig, BaseChipOps};
use halo2ecc_s::circuit::ecc_chip::{EccChipBaseOps, EccChipScalarOps};
use halo2ecc_s::circuit::integer_chip::IntegerChipOps;
use halo2ecc_s::circuit::range_chip::{RangeChip, RangeChipConfig};
use halo2ecc_s::context::{
    Context, GeneralScalarEccContext, IntegerContext, NativeScalarEccContext, Records,
};
use halo2ecc_s::utils::field_to_bn;

use halo2_proofs::dev::CircuitCost;

//use halo2::{
//    arithmetic::FieldExt,
//    circuit::{AssignedCell, Cell, Region, Value},
//};

//#[derive(Debug)]
//pub struct RegionCtx<'a, F: FieldExt> {
//    region: Region<'a, F>,
//    offset: usize,
//}
//
//impl<'a, F: FieldExt> RegionCtx<'a, F> {
//    pub fn new(region: Region<'a, F>, offset: usize) -> RegionCtx<'a, F> {
//        RegionCtx { region, offset }
//    }
//
//    pub fn offset(&self) -> usize {
//        self.offset
//    }
//
//    pub fn into_region(self) -> Region<'a, F> {
//        self.region
//    }
//
//    pub fn assign_fixed<A, AR>(
//        &mut self,
//        annotation: A,
//        column: Column<Fixed>,
//        value: F,
//    ) -> Result<AssignedCell<F, F>, Error>
//    where
//        A: Fn() -> AR,
//        AR: Into<String>,
//    {
//        self.region
//            .assign_fixed(annotation, column, self.offset, || Ok(value))
//    }
//
//    pub fn assign_advice<A, AR>(
//        &mut self,
//        annotation: A,
//        column: Column<Advice>,
//        value: F,
//    ) -> Result<AssignedCell<F, F>, Error>
//    where
//        A: Fn() -> AR,
//        AR: Into<String>,
//    {
//        self.region
//            .assign_advice(annotation, column, self.offset, || Ok(value))
//    }
//
//    pub fn constrain_equal(&mut self, cell_0: Cell, cell_1: Cell) ->
// Result<(), Error> {        self.region.constrain_equal(cell_0, cell_1)
//    }
//
//    pub fn enable(&mut self, selector: Selector) -> Result<(), Error> {
//        selector.enable(&mut self.region, self.offset)
//    }
//
//    pub fn next(&mut self) {
//        self.offset += 1
//    }
//}

/// Prints human-readable evaluation of circuit size and cost.
pub fn measure_circuit_size<G: PrimeGroup, C: Circuit<G::Scalar> + std::fmt::Debug>(
    circuit: &C,
    k: usize,
) where
    G::Scalar: FieldExt,
{
    //println!("{:?}", circuit);
    println!("{}", std::any::type_name::<C>());
    let cost: CircuitCost<_, _> = CircuitCost::<G, C>::measure(k, circuit);
    for (region, value) in &cost.regions {
        println!("  {}: {}", region, value);
    }

    println!("{:?}", cost);
    //
    //    //println!("min rows: {}", circuit.minimum_rows());
    //    let dimension = DimensionMeasurement::measure(circuit).unwrap();
    //    println!("{:?}", dimension);
}

#[derive(Clone, Debug)]
struct TestCircuitConfig {
    base_chip_config: BaseChipConfig,
    range_chip_config: RangeChipConfig,
}

fn random_bls12_381_fr() -> halo2_proofs::pairing::bls12_381::Fr {
    halo2_proofs::pairing::bls12_381::Fr::random(OsRng)
}

#[derive(Clone, Debug, Default)]
struct TestBLSCircuit {}

type N = <BN256_G1Affine as PrimeCurveAffine>::Scalar;

impl Circuit<N> for TestBLSCircuit {
    type Config = TestCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        let base_chip_config = BaseChip::configure(meta);
        let range_chip_config = RangeChip::<N>::configure(meta);
        TestCircuitConfig {
            base_chip_config,
            range_chip_config,
        }
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let base_chip = BaseChip::<N>::new(config.base_chip_config);
        let range_chip = RangeChip::<N>::new(config.range_chip_config);

        range_chip.init_table(&mut layouter)?;

        for BATCH_SIZE in [2, 4, 8, 16] {
            let (points, scalars) = layouter.assign_region(
                || format!("msm+assignment, batch size {:?}", BATCH_SIZE),
                |mut region| {
                    let ctx = Rc::new(RefCell::new(Context::new()));
                    let mut ctx = GeneralScalarEccContext::<G1Affine, Fr>::new(ctx);

                    let mut points = vec![];
                    let mut scalars = vec![];
                    let mut acc = G1::identity();

                    //let BATCH_SIZE = 16;
                    for _ in 0..BATCH_SIZE {
                        let a = random_bls12_381_fr();
                        let b = random_bls12_381_fr();
                        let p = G1::generator() * a;
                        acc = acc + p * b;
                        points.push(p);
                        scalars.push(b);
                    }

                    let points = points
                        .iter()
                        .map(|x| ctx.assign_point(x))
                        .collect::<Vec<_>>();
                    let scalars = scalars
                        .into_iter()
                        .map(|x| ctx.scalar_integer_ctx.assign_w(&field_to_bn(&x)))
                        .collect::<Vec<_>>();
                    //let res_expect: AssignedPoint<G1Affine, Fr> = ctx.assign_point(&acc);
                    let res: AssignedPoint<_, _> = ctx.msm(&points, &scalars);

                    //ctx.ecc_assert_equal(&res, &res_expect);

                    let ctx: Context<Fr> = ctx.into();
                    let records = std::sync::Arc::try_unwrap(ctx.records)
                        .unwrap()
                        .into_inner()
                        .unwrap();

                    records.assign_all(&mut region, &base_chip, &range_chip)?;
                    Ok((points.clone(), scalars.clone()))
                },
            )?;
        }

        Ok(())
    }
}

pub fn measure_ecc_bls12_circuits() {
    let circuit = TestBLSCircuit {};
    measure_circuit_size::<BN256_G1, _>(&circuit, 20);
}
