#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]

pub mod leanh {
    pub use leanh::*;
}

pub mod ffi {
    pub use gen_init::ffi::*;
    pub use gen_std::ffi::*;
    pub use gen_lean::ffi::*;
    pub use lake::ffi::*;
}

pub mod r#gen {
    pub use gen_init::r#gen::Init;
    pub use gen_std::r#gen::Std;
    pub use gen_lean::r#gen::Lean;
    pub use lake::r#gen::{Lake, LakeMain};
    pub mod LeanChecker {
        include!("gen/LeanChecker.rs");
    }
}
