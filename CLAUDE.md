# Catalia - Claude Reference

Catalia is a CHC solver (fork of HoIce) specialized for algebraic data types (ADTs). It solves CHC(ADT) by abstracting ADTs into CHC(LIA) using learned catamorphism-like encoders.

## Quick Commands

```bash
# Build and run (deletes hoice_out/)
./x -vvv <file.smt2>

# Run with timeout (recommended for non-termination issues)
timeout 30 ./x -vvv nagatomi.smt2 2>&1 | rg -n "Template:|new_encs:|checking enc refutes cex|Timeout or unknown"

# Run tests
cargo test --lib linear_approx_apply
cargo test --lib solve_by_blasting

# Direct run (preserves hoice_out/)
./target/debug/hoice --log_smt=on --log_preproc=on <file.smt2>
```

## Key Source Files

| File | Purpose |
|------|---------|
| `src/absadt.rs` | CEGAR loop orchestration, dump points |
| `src/absadt/enc.rs` | ADT → Int encoding semantics |
| `src/absadt/learn.rs` | Learning templates, scheduling, model collection |
| `src/absadt/chc.rs` | CEX (counterexample) format |

## Debug Artifacts

Located in `hoice_out/absadt/`:
- `target.smt2` - Original CHC(ADT) instance
- `encoded-epoch-<n>.smt2` - Encoded CHC(LIA) for epoch n (header shows encoders used)

## Core Concepts

- **Encoder/Catamorphism**: Maps each ADT constructor to an `Approx` producing an integer vector
- **n_params/n_encs**: Number of integer components (features) for an ADT encoding
- **Approx**: `{ args: VarInfos, terms: Vec<Term> }` - a lambda `\args. (terms...)`
- **CEX**: ADT-level SMT constraint `forall vars. term` from LIA counterexample
- **Epoch**: One CEGAR iteration (encode → backend solve → cex → check → learn/refine)

## CEGAR Loop (`AbsConf::run()`)

1. Initialize trivial encoders (all constructors → 0)
2. Encode CHC(ADT) → CHC(LIA) using current encoders
3. Call backend solver (HoIce/Spacer/Eldarica)
   - Safe → done
   - Counterexample → extract ADT-level CEX
4. Check CEX feasibility in original theory
   - Feasible → real counterexample (unsafe)
   - Infeasible → spurious; refine via `learn::work`
5. Repeat

## Learning (`LearnCtx::work`)

1. Check if current encoders refute CEX (solve under current encoders)
   - UNSAT → done
   - SAT → add model, continue
2. Refine encoders using templates from `TemplateScheduler`
3. Templates vary by `n_encs` (1,2,3...) and coefficient bounds

## Debugging "endless new_encs:"

Look for correlation between:
- `Template:` - which template is tried
- `new_encs:` - candidate encoder produced
- `checking enc refutes cex...` - whether it rules out models

If `new_encs` changes but never refutes CEX, suspect over-permissive template or need for structured templates (tags, recursion dependence).

## Runtime Dependencies

- Z3 via `rsmt2` for SMT solving
- Backend CHC solvers: HoIce, Spacer, Eldarica

## Testing Notes

### Global State Issue with Datatypes
HoIce keeps datatype constructors and selectors in global state. When running multiple test files, if two files define the same constructor name (e.g., `cons`, `nil`) for different datatypes, the second file will fail with:
```
constructor `cons` is already used by datatype `Lst`
```

**Solution**: Use unique constructor/selector names per test file. Convention: append a suffix derived from the file name (e.g., `LstTs`, `consTs`, `nilTs` for `two_sum.smt2`).

### Spacer Instability
Spacer may return "unknown" non-deterministically, especially in CI environments. This causes test failures.

**Solution**: Use Eldarica for counterexample generation in tests:
```bash
HOICE_USE_ELDARICA_CEX=1 cargo test
```

The `--eldarica-cex` CLI flag or `HOICE_USE_ELDARICA_CEX` environment variable enables Eldarica CEX mode.

### Eldarica vs Spacer CEX Format
- **Spacer**: Uses `query!X` as root node predicate in hyper-resolution proof
- **Eldarica**: Uses `FALSE` as root node predicate

Both are handled by `ResolutionProof::get_roots()` in `src/absadt/hyper_res.rs`.

### CI Eldarica Setup
When downloading Eldarica release archive, the extracted directory includes the version number (e.g., `eldarica-2.2.1/`). Add the root directory to PATH:
```yaml
- name: Install Eldarica
  run: |
    wget https://github.com/uuverifiers/eldarica/releases/download/v2.2.1/eldarica-bin-2.2.1.zip
    unzip eldarica-bin-2.2.1.zip
    mv eldarica-2.2.1 /usr/local/eldarica
    echo "/usr/local/eldarica" >> $GITHUB_PATH
```

