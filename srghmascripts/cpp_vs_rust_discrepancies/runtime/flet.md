# `runtime/flet` (`runtime/flet.h`)

## Location of corresponding Rust implementation
No corresponding Rust implementation exists. The `flet` template was a C++ RAII idiom used to temporarily mutate a value and restore it upon going out of scope. 

## Discrepancies and issues
This concept is generally unnecessary or handled differently in Rust, where temporary mutation is better avoided in favor of shadowing variables, functional updates, passing modified state down the call stack, or by using a custom struct that implements `Drop`. Given that it does not appear in the Rust implementation, the pattern was likely eliminated during porting in favor of more idiomatic Rust state management.
