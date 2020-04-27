#![feature(test)]
extern crate contracts;
extern crate test;

#[cfg(test)]
mod benchmark_tests {
    use contracts::*;
    use test::Bencher;
    build_bench_tests!();
}
