use crate::kernel_type_checker::initialize_type_checker::initialize_type_checker;

// In original C++, [`origin-master-src/kernel/init_module.cpp`](/home/srghma/projects/lean4/origin-master-src/kernel/init_module.cpp) does:
//
// 1. `initialize_level()`
// 2. `initialize_expr()`
// 3. `initialize_declaration()`
// 4. `initialize_type_checker()`
// 5. `initialize_environment()`
// 6. `initialize_local_ctx()`
// 7. `initialize_inductive()`
// 8. `initialize_quot()`
// 9. `initialize_trace()`
//
// So your current Rust file [`initialize_kernel_module.rs`](/home/srghma/projects/lean4/src/rust/leanh_l1_initializers/src/priv/initialize_kernel_module.rs) is not matching upstream if it only runs `initialize_type_checker()`.
//
// Also, the omitted three are not no-ops upstream:
//
// - [`origin-master-src/kernel/local_ctx.cpp`](/home/srghma/projects/lean4/origin-master-src/kernel/local_ctx.cpp)
//   - allocates and marks persistent `g_dummy_type` and `g_dummy_decl`
//
// - [`origin-master-src/kernel/inductive.cpp`](/home/srghma/projects/lean4/origin-master-src/kernel/inductive.cpp)
//   - initializes `_nested`, `_ind_fresh`, `_nested_fresh`
//   - builds persistent `Nat.zero`, `Nat.succ`, `String.ofList`
//   - builds `List.cons Char`, `List.nil Char`, `Char.ofNat`
//   - registers name-generator prefixes
//
// - [`origin-master-src/kernel/quot.cpp`](/home/srghma/projects/lean4/origin-master-src/kernel/quot.cpp)
//   - initializes persistent names `Quot`, `Quot.lift`, `Quot.ind`, `Quot.mk`
//
// So if Rust is trying to match C++, commenting those out is not correct unless that state is initialized somewhere else deliberately and equivalently.
pub fn initialize_kernel_module() {
    initialize_type_checker();
    // initialize_local_ctx();
    // initialize_inductive();
    // initialize_quot();
}
