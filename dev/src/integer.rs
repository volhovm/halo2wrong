use group::prime::PrimeGroup;
use integer::halo2::arithmetic::FieldExt;
use integer::halo2::circuit::{Layouter, SimpleFloorPlanner};
use integer::halo2::plonk::{Circuit, ConstraintSystem, Error};
use integer::rns::{Common, Integer, Rns};
use integer::{IntegerChip, IntegerConfig, IntegerInstructions, Range};
use maingate::{
    big_to_fe, MainGate, MainGateConfig, RangeChip, RangeConfig, RangeInstructions, RegionCtx,
};
use num_bigint::{BigUint as big_uint, RandBigInt};
use num_traits::Zero;
use rand_core::OsRng;
use std::rc::Rc;

use crate::util::measure_circuit_size;

const NUMBER_OF_LIMBS: usize = 4;

pub(crate) struct TestRNS<W: FieldExt, N: FieldExt, const BIT_LEN_LIMB: usize> {
    rns: Rc<Rns<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>>,
}

#[derive(Clone, Debug)]
struct TestCircuitConfig {
    range_config: RangeConfig,
    main_gate_config: MainGateConfig,
}

fn rns<W: FieldExt, N: FieldExt, const BIT_LEN_LIMB: usize>(
) -> Rns<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
    Rns::<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::construct()
}

fn setup<W: FieldExt, N: FieldExt, const BIT_LEN_LIMB: usize>(
) -> (Rns<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, u32) {
    let rns = rns();
    let k: u32 = (rns.bit_len_lookup + 1) as u32;
    (rns, k)
}

impl TestCircuitConfig {
    fn new<W: FieldExt, N: FieldExt, const BIT_LEN_LIMB: usize>(
        meta: &mut ConstraintSystem<N>,
    ) -> Self {
        let main_gate_config = MainGate::<N>::configure(meta);

        let overflow_bit_lens = rns::<W, N, BIT_LEN_LIMB>().overflow_lengths();
        let composition_bit_len =
            IntegerChip::<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::sublimb_bit_len();
        let range_config = RangeChip::<N>::configure(
            meta,
            &main_gate_config,
            vec![composition_bit_len],
            overflow_bit_lens,
        );

        TestCircuitConfig {
            range_config,
            main_gate_config,
        }
    }

    fn integer_chip_config(&self) -> IntegerConfig {
        IntegerConfig {
            range_config: self.range_config.clone(),
            main_gate_config: self.main_gate_config.clone(),
        }
    }

    fn config_range<N: FieldExt>(&self, layouter: &mut impl Layouter<N>) -> Result<(), Error> {
        let range_chip = RangeChip::<N>::new(self.range_config.clone());
        range_chip.load_table(layouter)?;

        Ok(())
    }
}

impl<W: FieldExt, N: FieldExt, const BIT_LEN_LIMB: usize> TestRNS<W, N, BIT_LEN_LIMB> {
    pub(crate) fn rand_in_field(&self) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        Integer::from_fe(W::random(OsRng), Rc::clone(&self.rns))
    }

    pub(crate) fn rand_in_remainder_range(&self) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        let el = OsRng.gen_biguint(self.rns.max_remainder.bits() as u64);
        Integer::from_big(el, Rc::clone(&self.rns))
    }

    pub(crate) fn rand_in_operand_range(&self) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        let el = OsRng.gen_biguint(self.rns.max_operand.bits() as u64);
        Integer::from_big(el, Rc::clone(&self.rns))
    }

    pub(crate) fn rand_in_unreduced_range(&self) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.rand_with_limb_bit_size(self.rns.max_unreduced_limb.bits() as usize)
    }

    pub(crate) fn rand_with_limb_bit_size(
        &self,
        bit_len: usize,
    ) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        let limbs = (0..NUMBER_OF_LIMBS)
            .map(|_| {
                let el = OsRng.gen_biguint(bit_len as u64);
                big_to_fe(el)
            })
            .collect::<Vec<N>>()
            .try_into()
            .unwrap();

        Integer::from_limbs(&limbs, Rc::clone(&self.rns))
    }

    pub(crate) fn new_from_big(&self, e: big_uint) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        Integer::from_big(e, Rc::clone(&self.rns))
    }

    pub(crate) fn new_from_limbs(
        &self,
        e: &[N; NUMBER_OF_LIMBS],
    ) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        Integer::from_limbs(e, Rc::clone(&self.rns))
    }

    pub(crate) fn max_in_remainder_range(&self) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.new_from_big(self.rns.max_remainder.clone())
    }

    pub(crate) fn max_in_operand_range(&self) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        self.new_from_big(self.rns.max_operand.clone())
    }

    // pub(crate) fn max_in_unreduced_range(
    //     &self,
    // ) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
    //     let limbs = [big_to_fe(self.rns.max_unreduced_limb.clone());
    // NUMBER_OF_LIMBS];     Integer::from_limbs(&limbs,
    // Rc::clone(&self.rns)) }

    pub fn zero(&self) -> Integer<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB> {
        Integer::from_big(big_uint::zero(), Rc::clone(&self.rns))
    }
}

macro_rules! impl_int_circuit {
    ($circuit_name:ident, $( $synth:tt )*) => {

        #[derive(Clone, Debug)]
        struct $circuit_name<W: FieldExt, N: FieldExt, const BIT_LEN_LIMB: usize> {
            rns: Rc<Rns<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>>,
        }

        impl<W: FieldExt, N: FieldExt,  const BIT_LEN_LIMB: usize> $circuit_name<W, N, BIT_LEN_LIMB> {
            fn integer_chip(&self, config:TestCircuitConfig) -> IntegerChip<W, N, NUMBER_OF_LIMBS,BIT_LEN_LIMB>{
                IntegerChip::<W, N, NUMBER_OF_LIMBS, BIT_LEN_LIMB>::new(config.integer_chip_config(), Rc::clone(&self.rns))
            }

            fn tester(&self) -> TestRNS<W, N, BIT_LEN_LIMB> {
                TestRNS {rns:Rc::clone(&self.rns)}
            }

        }

        impl<W: FieldExt, N: FieldExt,  const BIT_LEN_LIMB: usize> Circuit<N> for $circuit_name<W, N, BIT_LEN_LIMB> {
            type Config = TestCircuitConfig;
            type FloorPlanner = SimpleFloorPlanner;

            fn without_witnesses(&self) -> Self {
                unimplemented!();
            }

            fn configure(meta: &mut ConstraintSystem<N>) -> Self::Config {
                TestCircuitConfig::new::<W, N, BIT_LEN_LIMB>(meta)
            }

            $( $synth )*
        }
    };
}

impl_int_circuit!(
    TestCircuitRange,
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let integer_chip = self.integer_chip(config.clone());
        let t = self.tester();

        layouter.assign_region(
            || "region 0",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);
                let a = t.max_in_remainder_range();
                integer_chip.assign_integer(ctx, a.into(), Range::Remainder)?;
                // should fail
                // let a = t.new_from_big(rns.max_remainder.clone() + 1usize);
                // integer_chip.assign_integer(ctx, a.into(), Range::Remainder)?;
                let a = t.max_in_operand_range();
                integer_chip.assign_integer(ctx, a.into(), Range::Operand)?;
                // should fail
                // let a = t.new_from_big(rns.max_operand.clone() + 1usize);
                // integer_chip.assign_integer(ctx, a.into(), Range::Operand)?
                Ok(())
            },
        )?;
        config.config_range(&mut layouter)
    }
);

impl_int_circuit!(
    TestCircuitAddition,
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<N>,
    ) -> Result<(), Error> {
        let integer_chip = self.integer_chip(config.clone());
        let t = self.tester();
        layouter.assign_region(
            || "region 0",
            |region| {
                let offset = 0;
                let ctx = &mut RegionCtx::new(region, offset);

                {
                    let a = t.rand_in_remainder_range();
                    let b = t.rand_in_remainder_range();
                    let c = a.value() + b.value();
                    let c = t.new_from_big(c);

                    let c_in_field = (a.value() + b.value()) % &self.rns.wrong_modulus;
                    let c_in_field = t.new_from_big(c_in_field);
                    let a = integer_chip.assign_integer(ctx, a.into(), Range::Remainder)?;
                    let b = integer_chip.assign_integer(ctx, b.into(), Range::Remainder)?;

                    let c_0 = &integer_chip.add(ctx, &a, &b)?;
                    let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Unreduced)?;

                    assert_eq!(a.max_val() + b.max_val(), c_0.max_val());

                    integer_chip.assert_equal(ctx, c_0, &c_1)?;

                    // reduce and enfoce strict equality
                    let c_0 = integer_chip.reduce(ctx, c_0)?;
                    let c_1 =
                        integer_chip.assign_integer(ctx, c_in_field.into(), Range::Remainder)?;
                    integer_chip.assert_equal(ctx, &c_0, &c_1)?;
                    integer_chip.assert_strict_equal(ctx, &c_0, &c_1)?;
                }

                //{
                //    // constant addition in remainder range
                //    let a = t.rand_in_remainder_range();
                //    let b = t.rand_in_field();

                //    let c = a.value() + b.value();
                //    let c = t.new_from_big(c);
                //    let c_in_field = (a.value() + b.value()) % &self.rns.wrong_modulus;
                //    let c_in_field = t.new_from_big(c_in_field);

                //    let a = integer_chip.assign_integer(ctx, a.into(), Range::Remainder)?;

                //    let c_0 = &integer_chip.add_constant(ctx, &a, &b)?;
                //    let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Unreduced)?;
                //    assert_eq!(a.max_val() + b.value(), c_0.max_val());
                //    integer_chip.assert_equal(ctx, c_0, &c_1)?;

                //    // reduce and enfoce strict equality
                //    let c_0 = integer_chip.reduce(ctx, c_0)?;
                //    let c_1 =
                //        integer_chip.assign_integer(ctx, c_in_field.into(), Range::Remainder)?;
                //    integer_chip.assert_equal(ctx, &c_0, &c_1)?;
                //    integer_chip.assert_strict_equal(ctx, &c_0, &c_1)?;
                //}

                //{
                //    // go beyond unreduced range
                //    let a = t.rand_in_remainder_range();
                //    let mut a = integer_chip.assign_integer(ctx, a.into(), Range::Remainder)?;

                //    for _ in 0..10 {
                //        let c = a
                //            .integer()
                //            .map(|a| (a.value() * 2usize) % &self.rns.wrong_modulus)
                //            .map(|c| t.new_from_big(c));
                //        a = integer_chip.add(ctx, &a, &a)?;
                //        let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //        let c_0 = integer_chip.reduce(ctx, &a)?;
                //        integer_chip.assert_equal(ctx, &a, &c_1)?;
                //        integer_chip.assert_equal(ctx, &c_0, &c_1)?;
                //        integer_chip.assert_strict_equal(ctx, &c_0, &c_1)?;
                //    }
                //}

                //{
                //    // addition in unreduced range
                //    for _ in 0..10 {
                //        let a = t.rand_in_unreduced_range();
                //        let b = t.rand_in_unreduced_range();
                //        let c = (a.value() + b.value()) % self.rns.wrong_modulus.clone();
                //        let c = t.new_from_big(c);

                //        let a = integer_chip.assign_integer(ctx, a.into(), Range::Unreduced)?;
                //        let b = integer_chip.assign_integer(ctx, b.into(), Range::Unreduced)?;
                //        let c_0 = &integer_chip.add(ctx, &a, &b)?;
                //        let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //        assert_eq!(a.max_val() + b.max_val(), c_0.max_val());
                //        integer_chip.assert_equal(ctx, c_0, &c_1)?;

                //        // reduce and enfoce strict equality
                //        let c_0 = integer_chip.reduce(ctx, c_0)?;
                //        integer_chip.assert_equal(ctx, &c_0, &c_1)?;
                //        integer_chip.assert_strict_equal(ctx, &c_0, &c_1)?;
                //    }
                //}

                //{
                //    // subtraction in remainder range
                //    let a = t.rand_in_remainder_range();
                //    let b = t.rand_in_remainder_range();

                //    let a_norm = (a.value() % self.rns.wrong_modulus.clone())
                //        + self.rns.wrong_modulus.clone();
                //    let b_norm = b.value() % self.rns.wrong_modulus.clone();
                //    let c = (a_norm - b_norm) % self.rns.wrong_modulus.clone();
                //    let c = t.new_from_big(c);

                //    let a = integer_chip.assign_integer(ctx, a.into(), Range::Remainder)?;
                //    let b = integer_chip.assign_integer(ctx, b.into(), Range::Remainder)?;
                //    let aux = b.make_aux();

                //    let c_0 = &integer_chip.sub(ctx, &a, &b)?;
                //    let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //    assert_eq!(a.max_val() + aux.value(), c_0.max_val());
                //    integer_chip.assert_equal(ctx, c_0, &c_1)?;
                //}

                //{
                //    // subtraction in unreduced range
                //    let a = t.rand_in_unreduced_range();
                //    let b = t.rand_in_unreduced_range();

                //    let a_norm = (a.value() % self.rns.wrong_modulus.clone())
                //        + self.rns.wrong_modulus.clone();
                //    let b_norm = b.value() % self.rns.wrong_modulus.clone();
                //    let c = (a_norm - b_norm) % self.rns.wrong_modulus.clone();
                //    let c = t.new_from_big(c);

                //    let a = integer_chip.assign_integer(ctx, a.into(), Range::Unreduced)?;
                //    let b = integer_chip.assign_integer(ctx, b.into(), Range::Unreduced)?;
                //    let aux = b.make_aux();

                //    let c_0 = &integer_chip.sub(ctx, &a, &b)?;
                //    let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //    assert_eq!(a.max_val() + aux.value(), c_0.max_val());
                //    integer_chip.assert_equal(ctx, c_0, &c_1)?;
                //}

                //{
                //    // go beyond unreduced range
                //    let a = t.rand_in_remainder_range();
                //    let mut a = integer_chip.assign_integer(ctx, a.into(), Range::Remainder)?;

                //    for _ in 0..10 {
                //        let b = t.rand_in_unreduced_range();

                //        let a_norm = a.integer().map(|a| {
                //            a.value() % self.rns.wrong_modulus.clone()
                //                + self.rns.wrong_modulus.clone()
                //        });
                //        let b_norm = b.value() % self.rns.wrong_modulus.clone();
                //        let c = a_norm
                //            .map(|a_norm| (a_norm - b_norm) % self.rns.wrong_modulus.clone())
                //            .map(|c| t.new_from_big(c));

                //        let b = integer_chip.assign_integer(ctx, b.into(), Range::Unreduced)?;

                //        let c_0 = &integer_chip.sub(ctx, &a, &b)?;
                //        let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //        integer_chip.assert_equal(ctx, c_0, &c_1)?;
                //        a = c_0.clone();
                //    }
                //}

                //{
                //    // negation in unreduced range
                //    let a = t.rand_in_unreduced_range();
                //    let a_norm = a.value() % self.rns.wrong_modulus.clone();
                //    let c = self.rns.wrong_modulus.clone() - a_norm;
                //    let c = t.new_from_big(c);

                //    let a = integer_chip.assign_integer(ctx, a.into(), Range::Unreduced)?;
                //    let aux = a.make_aux();

                //    let c_0 = &integer_chip.neg(ctx, &a)?;
                //    let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //    assert_eq!(aux.value(), c_0.max_val());
                //    integer_chip.assert_equal(ctx, c_0, &c_1)?;
                //}

                //{
                //    // mul2 in unreduced range
                //    let a = t.rand_in_unreduced_range();
                //    let c = (a.value() * 2usize) % self.rns.wrong_modulus.clone();
                //    let c = t.new_from_big(c);

                //    let a = integer_chip.assign_integer(ctx, a.into(), Range::Unreduced)?;

                //    let c_0 = &integer_chip.mul2(ctx, &a)?;
                //    let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //    assert_eq!(a.max_val() * 2usize, c_0.max_val());
                //    integer_chip.assert_equal(ctx, c_0, &c_1)?;
                //}

                //{
                //    // mul3 in unreduced range
                //    let a = t.rand_in_unreduced_range();
                //    let c = (a.value() * 3usize) % self.rns.wrong_modulus.clone();
                //    let c = t.new_from_big(c);

                //    let a = integer_chip.assign_integer(ctx, a.into(), Range::Unreduced)?;
                //    let c_0 = &integer_chip.mul3(ctx, &a)?;
                //    let c_1 = integer_chip.assign_integer(ctx, c.into(), Range::Remainder)?;
                //    assert_eq!(a.max_val() * 3usize, c_0.max_val());
                //    integer_chip.assert_equal(ctx, c_0, &c_1)?;
                //}

                Ok(())
            },
        )?;
        config.config_range(&mut layouter)
    }
);

pub fn measure_integer_circuits() {
    use integer::halo2::halo2curves::bn256::{Fq as BnBase, Fr as BnScalar};
    use integer::halo2::halo2curves::pasta::{Ep as PastaEp, Eq as PastaEq};
    use integer::halo2::halo2curves::pasta::{Fp as PastaFp, Fq as PastaFq};
    use integer::halo2::halo2curves::secp256k1::{Fp as Secp256k1Base, Fq as Secp256k1Scalar};

    fn measure_range<G: PrimeGroup, W: FieldExt, const BIT_LEN_LIMB: usize>(k: u32)
    where
        G::Scalar: FieldExt,
    {
        let (rns, _): (Rns<W, G::Scalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, u32) = setup();
        let circuit = TestCircuitRange::<W, G::Scalar, BIT_LEN_LIMB> { rns: Rc::new(rns) };
        measure_circuit_size::<G, _>(&circuit, k);
    }

    measure_range::<PastaEq, PastaFq, 68>(10);
    measure_range::<PastaEq, PastaFp, 68>(10);
    measure_range::<PastaEq, BnBase, 68>(10);
    measure_range::<PastaEq, BnScalar, 68>(10);
    measure_range::<PastaEq, Secp256k1Base, 68>(10);
    measure_range::<PastaEq, Secp256k1Scalar, 68>(10);

    measure_range::<PastaEp, PastaFq, 68>(10);
    measure_range::<PastaEp, PastaFp, 68>(10);
    measure_range::<PastaEp, BnBase, 68>(10);
    measure_range::<PastaEp, BnScalar, 68>(10);
    measure_range::<PastaEp, Secp256k1Base, 68>(10);
    measure_range::<PastaEp, Secp256k1Scalar, 68>(10);

    fn measure_addition<G: PrimeGroup, W: FieldExt, const BIT_LEN_LIMB: usize>(k: u32)
    where
        G::Scalar: FieldExt,
    {
        let (rns, _): (Rns<W, G::Scalar, NUMBER_OF_LIMBS, BIT_LEN_LIMB>, u32) = setup();
        let circuit = TestCircuitAddition::<W, G::Scalar, BIT_LEN_LIMB> { rns: Rc::new(rns) };
        measure_circuit_size::<G, _>(&circuit, k);
    }

    measure_addition::<PastaEq, PastaFq, 68>(10);
    measure_addition::<PastaEq, PastaFp, 68>(10);
    measure_addition::<PastaEq, BnBase, 68>(10);
    measure_addition::<PastaEq, BnScalar, 68>(10);
    measure_addition::<PastaEq, Secp256k1Base, 68>(10);
    measure_addition::<PastaEq, Secp256k1Scalar, 68>(10);

    measure_addition::<PastaEp, PastaFq, 68>(10);
    measure_addition::<PastaEp, PastaFp, 68>(10);
    measure_addition::<PastaEp, BnBase, 68>(10);
    measure_addition::<PastaEp, BnScalar, 68>(10);
    measure_addition::<PastaEp, Secp256k1Base, 68>(10);
    measure_addition::<PastaEp, Secp256k1Scalar, 68>(10);
}
