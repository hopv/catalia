#!/bin/bash
set -eu
#cargo build --release
cargo build
rm -rf hoice_out
./target/debug/hoice --log_smt=on --log_preproc=on $@
