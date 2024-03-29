<h1 align="center">Accumulation Schemes</h1>

<p align="center">
    <img src="https://github.com/arkworks-rs/accumulation/workflows/CI/badge.svg?branch=main">
    <a href="https://github.com/arkworks-rs/accumulation/blob/main/LICENSE-APACHE">
        <img src="https://img.shields.io/badge/license-APACHE-blue.svg"></a>
    <a href="https://github.com/arkworks-rs/accumulation/blob/main/LICENSE-MIT">
        <img src="https://img.shields.io/badge/license-MIT-blue.svg"></a>
</p>

`ark-accumulation` is a Rust library that provides infrastructure for implementing 
*accumulation schemes*. This library was developed as part of the
[Proof-Carrying Data without Succinct Arguments][bclms20] paper, and is released under the MIT License
and the Apache v2 License (see [License](#license)).

**WARNING:** This is an academic prototype, and in particular has not received careful code review.
This implementation is NOT ready for production use.

## Overview

An accumulation scheme for a predicate is a cryptographic primitive that allows an accumulation
prover to receive a stream of inputs and accumulate them into an object called an *accumulator*.
Given the inputs and outputs of the prover, an accumulation verifier can verify that the set of
inputs was properly accumulated. At any time, an accumulation decider can use a single accumulator
to determine whether all the previously accumulated inputs satisfy the predicate.
 
This library provides the following features that enable specific implementations of accumulation
schemes:

- [`hp-as`](src/hp_as): An accumulation scheme for Hadamard Products

- [`ipa-pc-as`](src/ipa_pc_as): An accumulation scheme for the polynomial commitment scheme based on
Inner Product Arguments (as [implemented](
https://github.com/arkworks-rs/poly-commit/tree/accumulation-experimental/src/ipa_pc) in the
[`poly-commit`](https://github.com/arkworks-rs/poly-commit) library)

- [`r1cs-nark-as`](src/r1cs_nark_as): An accumulation scheme for a NARK for R1CS (as
[implemented](src/r1cs_nark_as/r1cs_nark) in this library)

- [`trivial-pc-as`](src/trivial_pc_as): An accumulation scheme for the trivial polynomial commitment
scheme (as [implemented](
https://github.com/arkworks-rs/poly-commit/tree/accumulation-experimental/src/trivial_pc) in the
[`poly-commit`](https://github.com/arkworks-rs/poly-commit) library)

## Build guide

The library compiles on the `stable` toolchain of the Rust compiler. To install the latest version
of Rust, first install `rustup` by following the instructions [here](https://rustup.rs/), or via
your platform's package manager. Once `rustup` is installed, install the Rust toolchain by invoking:
```bash
rustup install stable
```

After that, use `cargo` (the standard Rust build tool) to build the library:
```bash
git clone https://github.com/arkworks-rs/accumulation.git
cd accumulation
cargo build --release
```

This library comes with some unit and integration tests. Run these tests with:
```bash
cargo test
```

## License

This library is licensed under either of the following licenses, at your discretion.

 * [Apache License Version 2.0](LICENSE-APACHE)
 * [MIT License](LICENSE-MIT)

Unless you explicitly state otherwise, any contribution that you submit to this library shall be
dual licensed as above (as defined in the Apache v2 License), without any additional terms or
conditions.

## Reference papers

[Proof-Carrying Data from Accumulation Schemes][bcms20]     
Benedikt Bünz, Alessandro Chiesa, [Pratyush Mishra](https://www.github.com/pratyush),
Nicholas Spooner     

[Proof-Carrying Data without Succinct Arguments][bclms20]     
Benedikt Bünz, Alessandro Chiesa, [William Lin](https://github.com/Will-Lin4),
[Pratyush Mishra](https://www.github.com/pratyush), Nicholas Spooner     

[bcms20]: https://eprint.iacr.org/2020/499 
[bclms20]: https://eprint.iacr.org/2020/1618 
