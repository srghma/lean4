// Port of src/library/instantiate_mvars.cpp to Rust.
//
// instantiate_mvars.cpp exports two LEAN_EXPORT functions:
//   lean_instantiate_level_mvars  — instantiates level metavariables
//   lean_instantiate_expr_mvars   — two-pass expr MVar instantiation
//
// Both are deeply algorithmic (two C++ traversal passes, scope_cache,
// name_hash_map, pointer-identity caching) and operate entirely on C++
// lean::expr / lean::level / lean::name value types.  They stay in C++;
// Rust owns the exported symbols.

mod library_instantiate_mvars_impl {
    use super::*;

    extern "C" {
        fn lean_cxx_instantiate_level_mvars(
            mctx: *mut LeanObject,
            l: *mut LeanObject,
        ) -> *mut LeanObject;

        fn lean_cxx_instantiate_expr_mvars(
            mctx: *mut LeanObject,
            e: *mut LeanObject,
        ) -> *mut LeanObject;
    }

    /// `instantiateLevelMVars (mctx : MetavarContext) (l : Level) : MetavarContext × Level`
    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_level_mvars(
        mctx: *mut LeanObject,
        l: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_instantiate_level_mvars(mctx, l)
    }

    /// `instantiateExprMVars (mctx : MetavarContext) (e : Expr) : MetavarContext × Expr`
    #[no_mangle]
    pub unsafe extern "C" fn lean_instantiate_expr_mvars(
        mctx: *mut LeanObject,
        e: *mut LeanObject,
    ) -> *mut LeanObject {
        lean_cxx_instantiate_expr_mvars(mctx, e)
    }
}
