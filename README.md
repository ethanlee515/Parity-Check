# Parity Check

Hitting some error-correcting codes with cvc5.

## Usage

1. Modify "config.json" as needed
2. Generate SMT inputs by `./write_smt.py > 72-12-6-Z.smt2`
3. Feed the ".smt2" file into a solver such as cvc5

## Requirements

* Python with `numpy`, `scipy`, `galois`, and `json` packages
* Some kind of SMT solver (such as cvc5)
