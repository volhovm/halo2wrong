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

        let a_v = C::Curve::random(OsRng);
        let b_v = C::Curve::random(OsRng);
        let c_v = a_v + b_v;
        let d_v = a_v + a_v;
        let e_v = a_v + b_v + a_v;

        let mut offset = 0;
        let (a, a_0, b, c_0, d_0, e_0, mut offset) = layouter.assign_region(
            || "assign variables",
            |region| {
                let ctx = &mut RegionCtx::new(region, offset);

                //use integer::maingate::MainGateInstructions;
                //&ecc_chip.main_gate().break_here(ctx);

                let a = &ecc_chip.assign_point(ctx, Value::known(a_v.into()))?;
                let a_0 = &ecc_chip.assign_point(ctx, Value::known(a_v.into()))?;
                let b = &ecc_chip.assign_point(ctx, Value::known(b_v.into()))?;
                let c_0 = &ecc_chip.assign_point(ctx, Value::known(c_v.into()))?;
                let d_0 = &ecc_chip.assign_point(ctx, Value::known(d_v.into()))?;
                let e_0 = &ecc_chip.assign_point(ctx, Value::known(e_v.into()))?;

                Ok((
                    a.clone(),
                    a_0.clone(),
                    b.clone(),
                    c_0.clone(),
                    d_0.clone(),
                    e_0.clone(),
                    ctx.offset(),
                ))
            },
        )?;

        offset = layouter.assign_region(
            || "assert_equal",
            |region| {
                let ctx = &mut RegionCtx::new(region, offset);

                ecc_chip.assert_equal(ctx, &a, &a_0)?;

                Ok(ctx.offset())
            },
        )?;

        offset = layouter.assign_region(
            || "assert_is_on_curve",
            |region| {
                let ctx = &mut RegionCtx::new(region, offset);

                ecc_chip.assert_is_on_curve(ctx, &a)?;

                Ok(ctx.offset())
            },
        )?;

        offset = layouter.assign_region(
            || "neg",
            |region| {
                let ctx = &mut RegionCtx::new(region, offset);

                let _a_neg = ecc_chip.neg(ctx, &a)?;

                Ok(ctx.offset())
            },
        )?;

        offset = layouter.assign_region(
            || "addition",
            |region| {
                let ctx = &mut RegionCtx::new(region, offset);

                let _c_1 = &ecc_chip.add(ctx, &a, &b)?;

                Ok(ctx.offset())
            },
        )?;

        offset = layouter.assign_region(
            || "doubling",
            |region| {
                let ctx = &mut RegionCtx::new(region, offset);

                let _d_1 = &ecc_chip.double(ctx, &a)?;

                Ok(ctx.offset())
            },
        )?;

        offset = layouter.assign_region(
            || "ladder",
            |region| {
                let ctx = &mut RegionCtx::new(region, offset);

                //// test ladder

                let _e_1 = &ecc_chip.ladder(ctx, &a, &b)?;

                Ok(ctx.offset())
            },
        )?;

        config.config_range(&mut layouter)?;

        Ok(())
    }
}

pub fn measure_ecc_circuits() {
    fn measure_addition<
        G: PrimeGroup,
        C: CurveAffine,
        const NUMBER_OF_LIMBS: usize,
        const BIT_LEN_LIMB: usize,
    >(
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
    }

    use halo2::halo2curves::pasta::{Ep as PastaEp, Eq as PastaEq};

    measure_addition::<PastaEp, Bn256, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(20);
    measure_addition::<PastaEp, Secp256k1, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(20);
    measure_addition::<PastaEp, Pallas, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(20);

    measure_addition::<PastaEq, Bn256, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(20);
    measure_addition::<PastaEq, Secp256k1, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(20);
    measure_addition::<PastaEq, Vesta, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(20);

    measure_addition::<PastaEp, Bn256, 4, 72>(20);
    measure_addition::<PastaEp, Secp256k1, 4, 72>(20);
    measure_addition::<PastaEp, Pallas, 4, 72>(20);

    measure_addition::<PastaEq, Bn256, 4, 72>(20);
    measure_addition::<PastaEq, Secp256k1, 4, 72>(20);
    measure_addition::<PastaEq, Vesta, 4, 72>(20);
}
