fn main() {
    println!("Executing size estimator");
    dev::integer::measure_integer_circuits();
    dev::ecc::measure_ecc_circuits();
}
