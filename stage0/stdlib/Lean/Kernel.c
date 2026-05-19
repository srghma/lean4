// Lean compiler output
// Module: Lean.Kernel
// Imports: public import Lean.Kernel.Declaration public import Lean.Kernel.Level public import Lean.Kernel.Expr public import Lean.Kernel.LocalContext public import Lean.Kernel.Instantiate public import Lean.Kernel.ForEachExprV public import Lean.Kernel.PtrEq public import Lean.Kernel.EquivManager public import Lean.Kernel.Quot public import Lean.Kernel.Inductive.Reduce public import Lean.Kernel.TypeChecker public import Lean.Kernel.Environment
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* runtime_initialize_Lean_Kernel_Declaration(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Level(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_LocalContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Instantiate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_ForEachExprV(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_PtrEq(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_EquivManager(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Quot(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Inductive_Reduce(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Environment(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Kernel_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Instantiate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_ForEachExprV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_PtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_EquivManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Quot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Inductive_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Kernel_Declaration(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Level(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Expr(uint8_t builtin);
lean_object* initialize_Lean_Kernel_LocalContext(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Instantiate(uint8_t builtin);
lean_object* initialize_Lean_Kernel_ForEachExprV(uint8_t builtin);
lean_object* initialize_Lean_Kernel_PtrEq(uint8_t builtin);
lean_object* initialize_Lean_Kernel_EquivManager(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Quot(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Inductive_Reduce(uint8_t builtin);
lean_object* initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Kernel_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Instantiate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_ForEachExprV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_PtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_EquivManager(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Quot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Inductive_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel(builtin);
}
#ifdef __cplusplus
}
#endif
