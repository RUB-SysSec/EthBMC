extern crate contracts;

#[cfg(test)]
mod integration_tests {
    use contracts::*;
    build_integration_tests!();
}
