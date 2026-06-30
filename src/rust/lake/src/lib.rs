#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(
    unused_variables,
    unused_assignments,
    unused_parens,
    unused_mut,
    unused_imports
)]

pub mod ffi {
    // Re-export all public symbols from both crates into this unified module
    pub use gen_init_ffi::*;
    pub use gen_std_ffi::*;
    pub use gen_lean_ffi::*;
    pub use lake_ffi::*;
}

pub mod r#gen;
