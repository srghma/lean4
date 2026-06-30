#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(
    unused_variables,
    unused_assignments,
    unused_parens,
    unused_mut,
    unused_imports
)]

// TODO:
// maybe EmitRust instead of `use crate::ffi::lean_nat_add;`
// in `gen_std/src/gen/Std/Data/DHashMap/Internal/AssocList/Basic.rs:4:5`
// (lean_nat_add is from Init/Promise.lean)
// it should emit `gen_init::Init::Promise::lean_nat_add;`?

pub mod ffi {
    // Re-export all public symbols from both crates into this unified module
    pub use gen_init_ffi::*;
    pub use gen_std_ffi::*;
}

pub mod r#gen;
