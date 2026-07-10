# WORKSPACE ANALYSIS SUMMARY
========================================================================
Lean imports from Rust ([extern]): (Lean <- Rust)

| Label | Count |
| --- | ---: |
| Total occurrences: | 953 |
| Rust defined this function and function body is not empty (correct) (✅): | 425 |
| Rust defined this function but function body is empty (empty) (⚠️): | 0 |
| Rust does not define this function (missing) (❌): | 528 |

Rust should import from Lean ([export]): (Lean -> Rust)

| Label | Count |
| --- | ---: |
| Total occurrences: | 245 |
| Function is found in rust code and import is correct (correct) (✅): | 0 |
| Function is found in rust code, but import is wrong (wrong) (⚠️): | 15 |
| Function is found in rust code, but is defined in rust (defined) (🛠️): | 29 |
| Function is found inside of extern "C" block / FFI (externc) (🔌): | 79 |
| Function is referenced via dynamic string lookup (dynamic) (🔍): | 1 |
| Function is not found in rust code (missing) (❌): | 121 |
========================================================================
