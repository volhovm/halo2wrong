use ecc::general_ecc::GeneralEccChip;
use ecc::halo2;
use ecc::maingate;
use ecc::EccConfig;
use group::prime::PrimeGroup;
use group::Group;
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2::halo2curves::bn256::G1Affine as Bn256;
use halo2::halo2curves::pasta::{EpAffine as Pallas, EqAffine as Vesta};
use halo2::halo2curves::secp256k1::Secp256k1Affine as Secp256k1;
use halo2::plonk::{Circuit, ConstraintSystem, Error};
use maingate::{MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions, RegionCtx};
use rand_core::OsRng;
use std::marker::PhantomData;

use crate::util::measure_circuit_size;

const NUMBER_OF_LIMBS: usize = 4;
const BIT_LEN_LIMB: usize = 68;

#[derive(Clone, Debug)]
struct TestCircuitConfig {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
}

impl TestCircuitConfig {
    fn ecc_chip_config(&self) -> EccConfig {
        EccConfig {
            range_config: self.range_config.clone(),
            main_gate_config: self.main_gate_config.clone(),
        }
    }
}

impl TestCircuitConfig {
    fn new<C: CurveAffine, N: FieldExt, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>(
        meta: &mut ConstraintSystem<N>,
    ) -> Self {
        let (rns_base, rns_scalar) = GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::rns();

        let main_gate_config = MainGate::<N>::configure(meta);
        let mut overflow_bit_lens: Vec<usize> = vec![];
        overflow_bit_lens.extend(rns_base.overflow_lengths());
        overflow_bit_lens.extend(rns_scalar.overflow_lengths());
        let composition_bit_lens = vec![BIT_LEN_LIMB / NUMBER_OF_LIMBS];

        let range_config = RangeChip::<N>::configure(
            meta,
            &main_gate_config,
            composition_bit_lens,
            overflow_bit_lens,
        );

        TestCircuitConfig {
            main_gate_config,
            range_config,
        }
    }

    fn config_range<N: FieldExt>(&self, layouter: &mut impl Layouter<N>) -> Result<(), Error> {
        let range_chip = RangeChip::<N>::new(self.range_config.clone());
        range_chip.load_table(layouter)?;

        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
struct TestEccAddition<
    C: CurveAffine,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    _marker: PhantomData<(C, N)>,
}

impl<C: CurveAffine, N: FieldExt, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    Circuit<N> for TestEccAddition<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
{
    type Config = TestCircuitConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        unimplemented!()
    }

    fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
        TestCircuitConfig::new::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let ecc_chip_config = config.ecc_chip_config();
        let ecc_chip = GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(ecc_chip_config);
        layouter.assign_region(
            || "region 0",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                //use integer::maingate::MainGateInstructions;
                //&ecc_chip.main_gate().break_here(ctx);

                let a = C::Curve::random(OsRng);
                let b = C::Curve::random(OsRng);

                let c = a + b;
                let a = &ecc_chip.assign_point(ctx, Value::known(a.into()))?;
                let b = &ecc_chip.assign_point(ctx, Value::known(b.into()))?;
                let c_0 = &ecc_chip.assign_point(ctx, Value::known(c.into()))?;
                let c_1 = &ecc_chip.add(ctx, a, b)?;
                ecc_chip.assert_equal(ctx, c_0, c_1)?;

                //let c_1 = &ecc_chip.add(ctx, a, b)?;
                //ecc_chip.assert_equal(ctx, c_0, c_1)?;

                //// test doubling

                //let a = C::Curve::random(OsRng);
                //let c = a + a;

                //let a = &ecc_chip.assign_point(ctx, Value::known(a.into()))?;
                //let c_0 = &ecc_chip.assign_point(ctx, Value::known(c.into()))?;
                //let c_1 = &ecc_chip.double(ctx, a)?;
                //ecc_chip.assert_equal(ctx, c_0, c_1)?;

                //// test ladder

                //let a = C::Curve::random(OsRng);
                //let b = C::Curve::random(OsRng);
                //let c = a + b + a;

                //let a = &ecc_chip.assign_point(ctx, Value::known(a.into()))?;
                //let b = &ecc_chip.assign_point(ctx, Value::known(b.into()))?;
                //let c_0 = &ecc_chip.assign_point(ctx, Value::known(c.into()))?;
                //let c_1 = &ecc_chip.ladder(ctx, a, b)?;
                //ecc_chip.assert_equal(ctx, c_0, c_1)?;

                Ok(())
            },
        )?;

        config.config_range(&mut layouter)?;

        Ok(())
    }
}

pub fn measure_ecc_circuits() {
    fn run<G: PrimeGroup, C: CurveAffine, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>(
        k: u32,
    ) where
        <G as group::Group>::Scalar: FieldExt,
    {
        let circuit = TestEccAddition::<
            C,
            <G as group::Group>::Scalar,
            NUMBER_OF_LIMBS,
            BIT_LEN_LIMB,
        >::default();
        measure_circuit_size::<G, _>(&circuit, k);
        //mock_prover_verify(&circuit, instance);
    }

    use halo2::halo2curves::pasta::{Ep, Eq};

    run::<Ep, Bn256, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(12);
    run::<Ep, Secp256k1, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(12);
    run::<Ep, Pallas, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(12);

    run::<Eq, Bn256, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(12);
    run::<Eq, Secp256k1, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(12);
    run::<Eq, Vesta, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(12);

    //    run::<Bn256, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
    //    run::<Bn256, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
    //    run::<Bn256, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
    //
    //    run::<Secp256k1, BnScalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
    //    run::<Secp256k1, PastaFp, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
    //    run::<Secp256k1, PastaFq, NUMBER_OF_LIMBS, BIT_LEN_LIMB>();
}
