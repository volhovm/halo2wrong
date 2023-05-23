fn main() {
    println!("Executing circuit estimator");
    //dev::integer::measure_integer_circuits();
    //dev::ecc::measure_ecc_circuits();
    //dev::ecc_bls12_381::measure_ecc_bls12_circuits();

    dev::util::simple_msm_estimator();
}
