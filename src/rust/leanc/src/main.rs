#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(
    unused_variables,
    unused_assignments,
    unused_parens,
    unused_mut,
    unused_imports
)]

pub mod r#gen {
    pub use lake::r#gen::{Lake, LakeMain};
    pub mod Leanc {
        include!("gen/Leanc.rs");
    }
}
