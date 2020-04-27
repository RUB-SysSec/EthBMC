#!/bin/sh

echo "# =================================================="
echo "# Running Unit Tests"
echo "# =================================================="

cargo test -- --test-threads=1

echo "# =================================================="
echo "# Running Expensive & Parity Dependent Tests"
echo "# =================================================="

cargo test se --release -- --ignored --test-threads=1

echo "# =================================================="
echo "# Running Integration Tests"
echo "# =================================================="

cargo test integra --release -- --ignored
