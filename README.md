# Catalia

**Catalia** is a CHC solver specialized for algebraic data types, forked from [HoIce](https://github.com/hopv/hoice). While much of the codebase remains the same, we maintain Catalia as a separate solver due to the following reasons:

1. Catalia utilizes only the frontend parts of HoIce (e.g., parsing and clause manipulation) and does not rely on its Ice component.
2. Unlike HoIce, Catalia employs multiple CHC solvers as Catalia's backend solver, including HoIce, Spacer, and Eldarica (see our paper for technical details). Since this approach differs significantly from a mere extension of HoIce, we have opted to maintain a separate repository to reflect this distinction.


# HoIce (original README)

`hoice` is an ICE-based Constrained Horn Clause (CHC) solver.

Given some CHCs mentioning some undefined predicates, hoice infers definitions for these predicate
that respect all CHCs or prove none exist. Hoice supports the `Bool`, `Int` and `Real` sorts. It
also supports user-defined ADTs, although it is still in an experimental stage.

# Install

If you haven't already, install [Rust](https://www.rust-lang.org) on your system. The recommended way to do this is to use [`rustup`](https://www.rustup.rs/).

Hoice generally uses the latest rust features available. Make sure the rust ecosystem is up to date by running the following command before building hoice.

```bash
rustup update stable
```

Installing hoice with `cargo`:

```bash
cargo install --git https://github.com/hopv/hoice
```

To build hoice manually, clone this repository, `cd` in the directory and run

```bash
cargo build --release
```
The binary file will be in `target/release/hoice`.

To get the fastest version, compile hoice with

```bash
cargo build --release --features "bench"
```

Note that this disables some features such as verbose output, profiling...


## z3

`hoice` relies on the [z3](https://github.com/Z3Prover/z3) SMT-solver. Make sure you have a relatively recent version of the z3 binary in your path.


# Language

[Consult the wiki](https://github.com/hopv/hoice/wiki/Language) for a description of `hoice`'s language.


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


# Checking the result

`hoice` can check its own results. The code performing this feature is completely separated from the code doing the actual inference so that the check is meaningful.

In fact, the code for this is almost implemented as some string substitutions followed by an SMT query for each clause of the problem.

For now, this feature is completely off-line. Put `hoice`'s result in a file, for instance with

```bash
hoice <horn_clause_file> | tee <output_file>
```

and use the `--check` option to verify that the predicates inferred verify all the horn clauses:

```bash
hoice --check <output_file> <horn_clause_file>
```


# Latest version

This repository hosts the latest stable version of hoice. See the [main
developer's fork][main dev fork] for a cutting edge, although unstable,
version.


# Contributing

We welcome any help, please the [contribution guidelines](https://github.com/hopv/hoice/wiki/Contributing) if you are not familiar with the github pull request workflow to get started.


# License

`hoice` is released under the [Apache 2 license](./LICENSE.md). Please note in particular that the [`NOTICE.md`](./NOTICE.md) file from this repository must be available if you redistribute `hoice` in a source or binary format.

[benchs]: https://github.com/hopv/benchmarks/tree/master/clauses (hopv benchmarks)
[main dev fork]: https://github.com/AdrienChampion/hoice (AdrienChampion's fork of hoice on github)
