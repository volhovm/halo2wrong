use ecc::general_ecc::GeneralEccChip;
use ecc::halo2;
use ecc::maingate;
use ecc::EccConfig;
use group::ff::Field;
use group::prime::PrimeGroup;
use group::{Curve, Group};
use halo2::arithmetic::{CurveAffine, FieldExt};
use halo2::circuit::{Layouter, SimpleFloorPlanner, Value};
use halo2::halo2curves::bn256::G1Affine as Bn256;
use halo2::halo2curves::pasta::{EpAffine as Pallas, EqAffine as Vesta};
use halo2::halo2curves::secp256k1::Secp256k1Affine as Secp256k1;
use halo2::plonk::{Circuit, ConstraintSystem, Error};
use integer::rns::Integer;
use integer::{IntegerInstructions, Range};
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
struct EccEvaluation<
    C: CurveAffine,
    N: FieldExt,
    const NUMBER_OF_LIMBS: usize,
    const BIT_LEN_LIMB: usize,
> {
    _marker: PhantomData<(C, N)>,
}

impl<C: CurveAffine, N: FieldExt, const NUMBER_OF_LIMBS: usize, const BIT_LEN_LIMB: usize>
    Circuit<N> for EccEvaluation<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>
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
        let mut ecc_chip =
            GeneralEccChip::<C, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(ecc_chip_config);

        let aux_generator = C::Curve::random(OsRng).to_affine();
        let a_v = C::Curve::random(OsRng);
        let b_v = C::Curve::random(OsRng);
        let s_v = C::Scalar::random(OsRng);
        let s_v = Integer::from_fe(s_v, ecc_chip.rns_scalar());

        let number_of_pairs = 16;
        let batch_pairs: Vec<_> = (0..number_of_pairs)
            .map(|_| {
                let base = C::Curve::random(OsRng);
                let s = C::Scalar::random(OsRng);
                let s = Integer::from_fe(s, ecc_chip.rns_scalar());
                Ok((base, s))
            })
            .collect::<Result<_, Error>>()?;

        let (a, a_0, b, s, pairs_assigned) = layouter.assign_region(
            || "assign variables",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                //use integer::maingate::MainGateInstructions;
                //&ecc_chip.main_gate().break_here(ctx);

                ecc_chip.assign_aux_generator(ctx, Value::known(aux_generator))?;

                let a = &ecc_chip.assign_point(ctx, Value::known(a_v.into()))?;
                let a_0 = &ecc_chip.assign_point(ctx, Value::known(a_v.into()))?;
                let b = &ecc_chip.assign_point(ctx, Value::known(b_v.into()))?;
                let s = &ecc_chip.scalar_field_chip().assign_integer(
                    ctx,
                    Value::known(s_v.clone()).into(),
                    Range::Remainder,
                )?;

                let pairs_assigned: Vec<_> = batch_pairs
                    .iter()
                    .map(|(base, s)| {
                        let base = ecc_chip.assign_point(ctx, Value::known(base.clone().into()))?;
                        let s = ecc_chip.scalar_field_chip().assign_integer(
                            ctx,
                            Value::known(s.clone()).into(),
                            Range::Remainder,
                        )?;
                        Ok((base, s))
                    })
                    .collect::<Result<_, Error>>()?;

                Ok((
                    a.clone(),
                    a_0.clone(),
                    b.clone(),
                    s.clone(),
                    pairs_assigned.clone(),
                ))
            },
        )?;

        layouter.assign_region(
            || "assert_equal",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);

                ecc_chip.assert_equal(ctx, &a, &a_0)?;

                Ok(())
            },
        )?;

        layouter.assign_region(
            || "assert_is_on_curve",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                ecc_chip.assert_is_on_curve(ctx, &a)?;
                Ok(())
            },
        )?;

        layouter.assign_region(
            || "neg",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let _a_neg = ecc_chip.neg(ctx, &a)?;
                Ok(())
            },
        )?;

        layouter.assign_region(
            || "addition",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let _c_1 = &ecc_chip.add(ctx, &a, &b)?;
                Ok(())
            },
        )?;

        layouter.assign_region(
            || "doubling",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let _d_1 = &ecc_chip.double(ctx, &a)?;
                Ok(())
            },
        )?;

        layouter.assign_region(
            || "ladder",
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let _e_1 = &ecc_chip.ladder(ctx, &a, &b)?;
                Ok(())
            },
        )?;

        // 3 is optimal with common parameters.
        let window_size = 3;
        layouter.assign_region(
            || format!("mul pre-assign windows {}", window_size),
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                ecc_chip.assign_aux(ctx, window_size, 1)?;
                Ok(())
            },
        )?;
        layouter.assign_region(
            || format!("mul window {}", window_size),
            |region| {
                let ctx = &mut RegionCtx::new(region, 0);
                let _ret = ecc_chip.mul(ctx, &b, &s, window_size)?;
                Ok(())
            },
        )?;

        for batch_size in [2, 4, 8, 16] {
            layouter.assign_region(
                || {
                    format!(
                        "batch mul pre-assign pairs {} window {}",
                        batch_size, window_size
                    )
                },
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    ecc_chip.assign_aux(ctx, window_size, batch_size)?;
                    Ok(())
                },
            )?;

            layouter.assign_region(
                || format!("batch size {} mul window {}", batch_size, window_size),
                |region| {
                    let ctx = &mut RegionCtx::new(region, 0);
                    let _res = ecc_chip.mul_batch_1d_horizontal(
                        ctx,
                        (&pairs_assigned.as_slice())[0..batch_size].to_vec(),
                        window_size,
                    )?;
                    Ok(())
                },
            )?;
        }

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
        let circuit =
            EccEvaluation::<C, <G as group::Group>::Scalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::default(
            );
        measure_circuit_size::<G, _>(&circuit, k);
    }

    use halo2::halo2curves::pasta::{Ep as PastaEp, Eq as PastaEq};

    let k = 25;

    measure_addition::<PastaEp, Bn256, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(k);
    //measure_addition::<PastaEp, Secp256k1, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(k);
    //measure_addition::<PastaEp, Vesta, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(k);

    //measure_addition::<PastaEq, Bn256, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(k);
    //measure_addition::<PastaEq, Secp256k1, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(k);
    //measure_addition::<PastaEq, Pallas, NUMBER_OF_LIMBS, BIT_LEN_LIMB>(k);

    //measure_addition::<PastaEp, Bn256, 4, 72>(k);
    //measure_addition::<PastaEp, Secp256k1, 4, 72>(k);
    //measure_addition::<PastaEp, Pallas, 4, 72>(k);

    //measure_addition::<PastaEq, Bn256, 4, 72>(k);
    //measure_addition::<PastaEq, Secp256k1, 4, 72>(k);
    //measure_addition::<PastaEq, Vesta, 4, 72>(k);
}
