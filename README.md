# Catalia

**Catalia** is a CHC solver specialized for algebraic data types, forked from [HoIce](https://github.com/hopv/hoice). While much of the codebase remains the same, we maintain Catalia as a separate solver due to the following reasons:

1. Catalia utilizes only the frontend parts of HoIce (e.g., parsing and clause manipulation) and does not rely on its Ice component.
2. Unlike HoIce, Catalia employs multiple CHC solvers as Catalia's backend solver, including HoIce, Spacer, and Eldarica (see our paper for technical details). Since this approach differs significantly from a mere extension of HoIce, we have opted to maintain a separate repository to reflect this distinction.


# Install

If you haven't already, install [Rust](https://www.rust-lang.org) on your system. The recommended way to do this is to use [`rustup`](https://www.rustup.rs/).

Catalia generally uses the latest rust features available. Make sure the rust ecosystem is up to date by running the following command before building catalia.

```bash
rustup update stable
```

Installing catalia with `cargo`:

```bash
cargo install --git https://github.com/hopv/catalia
```

To build catalia manually, clone this repository, `cd` in the directory and run

```bash
cargo build --release
```
The binary file will be in `target/release/hoice`.

To get the fastest version, compile catalia with

```bash
cargo build --release --features "bench"
```

Note that this disables some features such as verbose output, profiling...


## Dependencies on External Solvers

Catalia depends on the following external solvers:
- Required: 
  -  [z3](https://github.com/Z3Prover/z3) (recommended: version **4.12.0**)
- Recommended:
If available, these solvers are used as backend solvers for solving CHC(LIA) problems.
(Note: Catalia does not use the CHC(ADT) components of these solvers.)
   - [HoIce](https://github.com/hopv/hoice)
   - [Eldarica](https://github.com/uuverifiers/eldarica)

Please ensure that your Z3 binary is available in your PATH.
Catalia is known **not** to work with some versions of Z3. 
We confirm that it works as expected with Z3 version 4.12.0.
If Catalia does not work as expected, please check the version of Z3 you are using carefully (sorry for this).


# Language

[Consult the wiki](https://github.com/hopv/hoice/wiki/Language) for a description of `catalia`'s language.


# Features

- [x] `define-fun`s
- [x] `Bool`
- [x] `Int`
- [x] `Real`
- [x] `Array` (naive)
- [x] `List`
- [x] (mutually recursive) ADTs

Future features:

- [ ] user-specified qualifiers through `define-fun`s

# Latest version

This repository hosts the latest stable version of catalia. See the [main
developer's fork](https://github.com/moratorium08/hoice) for a cutting edge, although unstable,
version.


# Contributing

We welcome any help, please the [contribution guidelines](https://github.com/hopv/hoice/wiki/Contributing) if you are not familiar with the github pull request workflow to get started.


# License

`catalia` is released under the [Apache 2 license](./LICENSE.md). Please note in particular that the [`NOTICE.md`](./NOTICE.md) file from this repository must be available if you redistribute `catalia` in a source or binary format.
