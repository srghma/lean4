#![allow(dead_code, non_upper_case_globals, non_snake_case)]
#![allow(unused_variables, unused_assignments, unused_parens, unused_mut, unused_imports)]

pub mod leanh {
    pub use lean_runtime_common::leanh::*;
}

pub mod lean_imports_rs {
    pub use lean_runtime_common::lean_imports_rs::*;
}

pub mod r#gen {
    pub use lean_gen_init::r#gen::Init;
    pub use lean_gen_std::r#gen::Std;
    pub use lean_gen_lean::r#gen::Lean;
    pub use lean_gen_lake::r#gen::Lake;
    pub use lean_gen_lake::r#gen::LakeMain;
    pub mod Leanc {
        include!("../../lean_runtime/src/gen/Leanc.rs");
    }
    pub mod LeanChecker {
        include!("../../lean_runtime/src/gen/LeanChecker.rs");
    }
    pub mod LeanIR {
        include!("../../lean_runtime/src/gen/LeanIR.rs");
    }
}
