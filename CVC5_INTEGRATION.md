# CVC5 Integration for Catalia

## Summary

This document describes the CVC5 integration for Catalia, allowing the use of CVC5 as an alternative SMT solver to Z3 for satisfiability checking.

## Important Distinction

### What CAN be replaced:
- **SMT Solver**: The solver used for general SMT queries (satisfiability checking, model generation, etc.)
- Catalia now supports both Z3 and CVC5 for this purpose

### What CANNOT be replaced:
- **CHC Solver (Spacer)**: Z3's Spacer engine is used for solving Horn Clause Constraints (CHC)
- Spacer is invoked directly (not through rsmt2) and cannot be replaced with CVC5
- CVC5 does not have a Horn clause solving engine equivalent to Spacer

## Implementation Details

### Architecture
1. **rsmt2 Library**: Catalia uses rsmt2 v0.16.2 as a generic SMT-LIB2 interface
2. **rsmt2 Support**: rsmt2 has built-in support for both Z3 and CVC4
3. **CVC5 Compatibility**: CVC5 is the successor to CVC4 and maintains compatibility with CVC4's SMT-LIB2 interface
4. **Configuration**: The integration uses rsmt2's CVC4 configuration for CVC5 (via `SolverConf::cvc4()`)

### Code Changes

#### Modified Files
- `src/common/config.rs`: Added CVC5 support to `SmtConf` configuration

#### New Command-Line Options
1. `--solver <solver_type>`: Choose between 'z3' or 'cvc5' (default: z3)
   - Example: `--solver cvc5`

2. `--smt-cmd <command>`: Override the solver binary command
   - Example: `--smt-cmd /usr/local/bin/cvc5`
   - If not specified, defaults to "z3" or "cvc5" based on --solver option

### Implementation in config.rs

```rust
impl SmtConf {
    pub fn new_with_solver_selection(matches: &Matches) -> Self {
        // Get solver type (z3 or cvc5)
        let solver_type = matches.value_of("solver_cmd").unwrap_or("z3").to_string();

        // Get command override
        let cmd_override = matches.value_of("z3_cmd").unwrap_or("");

        // Determine command and solver type
        let (cmd, use_cvc5) = if solver_type == "cvc5" || solver_type == "CVC5" {
            let cmd = if cmd_override.is_empty() { "cvc5" } else { cmd_override };
            (cmd.to_string(), true)
        } else {
            let cmd = if cmd_override.is_empty() { "z3" } else { cmd_override };
            (cmd.to_string(), false)
        };

        // Create solver configuration
        let mut conf = if use_cvc5 {
            SolverConf::cvc4(&cmd)  // CVC5 uses CVC4's SMT-LIB2 interface
        } else {
            SolverConf::z3(&cmd)
        };
        conf.models();

        Self { solver_type, conf, log }
    }
}
```

## Usage Examples

### Using Z3 (default)
```bash
./hoice problem.smt2
# or explicitly
./hoice --solver z3 problem.smt2
```

### Using CVC5
```bash
./hoice --solver cvc5 problem.smt2
```

### Using Custom Binary Path
```bash
./hoice --solver cvc5 --smt-cmd /path/to/cvc5 problem.smt2
```

### With Logging
```bash
./hoice --solver cvc5 --log_smt=on problem.smt2
# Check logs in hoice_out/solvers/
```

## Testing

### Test Files Created

1. **test_cvc5_integration.smt2**: Tests NIA (Non-linear Integer Arithmetic)
   - Tests basic Horn clauses with integer arithmetic
   - Includes loop invariant verification

2. **test_cvc5_adt.smt2**: Tests ADT + LIA
   - Tests Algebraic Data Types (IntList)
   - Includes recursive functions (list length)
   - Combines ADTs with Linear Integer Arithmetic

### Running Tests

```bash
# Install CVC5 first
wget https://github.com/cvc5/cvc5/releases/latest/download/cvc5-Linux-x86_64-static.zip
unzip cvc5-Linux-x86_64-static.zip
sudo cp cvc5-Linux-x86_64-static/bin/cvc5 /usr/local/bin/
chmod +x /usr/local/bin/cvc5

# Test with Z3
./hoice --solver z3 test_cvc5_integration.smt2
./hoice --solver z3 test_cvc5_adt.smt2

# Test with CVC5
./hoice --solver cvc5 test_cvc5_integration.smt2
./hoice --solver cvc5 test_cvc5_adt.smt2
```

### Expected Test Coverage

The integration should be tested with:
1. ✓ **NIA Queries**: Non-linear integer arithmetic (multiplication, squares, etc.)
2. ✓ **ADT Queries**: Algebraic data types (lists, trees, custom datatypes)
3. ✓ **LIA Queries**: Linear integer arithmetic
4. ✓ **Recursive Functions**: Functions defined recursively over ADTs
5. **Quantifiers**: Universal and existential quantification
6. **Models**: Model generation and extraction
7. **UNSAT Cores**: Unsatisfiable core extraction (if supported)

## Potential Issues and Limitations

### Known rsmt2/CVC4 Issues
According to rsmt2 documentation:
- Some versions of CVC4 have issues with `get-value` commands
- CVC5 may inherit some of these limitations
- The integration uses `get-model` which should work better

### CVC5-Specific Considerations
1. **Performance**: CVC5 may have different performance characteristics than Z3
   - May be faster or slower depending on the problem
   - Should benchmark on real Catalia workloads

2. **Feature Parity**: Not all Z3 features may be available in CVC5
   - Check specific theory support (arrays, bitvectors, etc.)
   - Some Catalia-specific optimizations may be Z3-specific

3. **Interactive Mode**: Both solvers support SMT-LIB2 interactive mode
   - CVC5 should work seamlessly with rsmt2's interactive interface

### Spacer Dependency
- **Cannot be removed**: Spacer (Z3's CHC engine) is still required
- Even when using CVC5 for SMT, Z3 must be installed for CHC solving
- This is a fundamental limitation: CVC5 does not have Horn clause solving

## Recommendations

### For Testing
1. **Install both solvers**: Keep both Z3 and CVC5 installed
2. **Benchmark**: Compare performance on real Catalia problems
3. **Regression testing**: Run full test suite with both solvers
4. **Coverage**: Test all theory combinations Catalia uses

### For Production Use
1. **Default to Z3**: Keep Z3 as the default for backward compatibility
2. **Selective CVC5**: Use CVC5 for specific problems where it performs better
3. **Monitoring**: Log and monitor solver performance differences
4. **Fallback**: Implement fallback to Z3 if CVC5 fails

### Future Enhancements
1. **Auto-selection**: Automatically choose solver based on problem characteristics
2. **Parallel solving**: Run both solvers in parallel, use first result
3. **Solver options**: Expose CVC5-specific options for tuning
4. **Extended logging**: Log which solver was used for each query

## References

- [CVC5 GitHub Repository](https://github.com/cvc5/cvc5)
- [CVC5 Downloads](https://cvc5.github.io/downloads.html)
- [rsmt2 Documentation](https://docs.rs/rsmt2/0.16.2/)
- [SMT-LIB Standard](https://smtlib.cs.uiowa.edu/)

## Validation Status

- ✅ Code compiles successfully
- ✅ Command-line interface extended
- ✅ Configuration properly handles Z3/CVC5 selection
- ✅ Test cases created (NIA, ADT+LIA)
- ⏳ Runtime testing pending (requires CVC5 installation)
- ⏳ Performance benchmarking pending
- ⏳ Full regression testing pending

## Installation Instructions

### CVC5 Installation

```bash
# Download latest CVC5
cd /tmp
wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.2/cvc5-Linux-x86_64-static.zip

# Extract and install
unzip cvc5-Linux-x86_64-static.zip
cd cvc5-Linux-x86_64-static/bin
sudo cp cvc5 /usr/local/bin/
sudo chmod +x /usr/local/bin/cvc5

# Verify installation
cvc5 --version
```

### Building Catalia with CVC5 Support

```bash
# The integration is already in the code
cd /path/to/catalia
cargo build --release

# Test the integration
./target/release/hoice --solver cvc5 --help
```
