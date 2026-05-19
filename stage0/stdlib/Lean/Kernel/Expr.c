// Lean compiler output
// Module: Lean.Kernel.Expr
// Imports: public import Lean.Environment
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
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_instBEqPtr___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_instHashablePtr___lam__0___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* l_Lean_mkPtrMap___redArg(lean_object*);
static lean_once_cell_t l_Lean_Expr_prop___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_prop___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_prop;
static const lean_string_object l_Lean_Expr_arrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Expr_arrow___closed__0 = (const lean_object*)&l_Lean_Expr_arrow___closed__0_value;
static const lean_ctor_object l_Lean_Expr_arrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_arrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Expr_arrow___closed__1 = (const lean_object*)&l_Lean_Expr_arrow___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_arrow(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_lam0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l_Lean_Expr_lam0___closed__0 = (const lean_object*)&l_Lean_Expr_lam0___closed__0_value;
static const lean_ctor_object l_Lean_Expr_lam0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_lam0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(168, 60, 211, 188, 58, 220, 100, 184)}};
static const lean_object* l_Lean_Expr_lam0___closed__1 = (const lean_object*)&l_Lean_Expr_lam0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_lam0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cacheT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqPtr___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0_value;
static const lean_closure_object l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashablePtr___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cacheT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cacheT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Lean.Expr"};
static const lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__0_value;
static const lean_string_object l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateMData!Impl"};
static const lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__1_value;
static const lean_string_object l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "mdata expected"};
static const lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "_private.Lean.Expr.0.Lean.Expr.updateProj!Impl"};
static const lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__0 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__0_value;
static const lean_string_object l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "proj expected"};
static const lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__1 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__1_value;
static lean_once_cell_t l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__13(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__15(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__2(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__4(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__8(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_natZero___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Expr_natZero___closed__0 = (const lean_object*)&l_Lean_Expr_natZero___closed__0_value;
static const lean_string_object l_Lean_Expr_natZero___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "zero"};
static const lean_object* l_Lean_Expr_natZero___closed__1 = (const lean_object*)&l_Lean_Expr_natZero___closed__1_value;
static const lean_ctor_object l_Lean_Expr_natZero___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_natZero___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Expr_natZero___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_natZero___closed__2_value_aux_0),((lean_object*)&l_Lean_Expr_natZero___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 81, 163, 94, 71, 156, 90, 186)}};
static const lean_object* l_Lean_Expr_natZero___closed__2 = (const lean_object*)&l_Lean_Expr_natZero___closed__2_value;
static lean_once_cell_t l_Lean_Expr_natZero___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_natZero___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_natZero;
static const lean_string_object l_Lean_Expr_natSucc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Expr_natSucc___closed__0 = (const lean_object*)&l_Lean_Expr_natSucc___closed__0_value;
static const lean_ctor_object l_Lean_Expr_natSucc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_natZero___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Expr_natSucc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_natSucc___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_natSucc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Expr_natSucc___closed__1 = (const lean_object*)&l_Lean_Expr_natSucc___closed__1_value;
static lean_once_cell_t l_Lean_Expr_natSucc___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_natSucc___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_natSucc;
LEAN_EXPORT lean_object* l_Lean_Expr_isConstructorApp_x3f_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_isConstructorApp_x3f_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_natLitToConstructor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_natLitToConstructor___boxed(lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Char"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__2_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(27, 51, 10, 169, 25, 67, 44, 251)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__3;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__4_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__5_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cons"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__7_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(98, 170, 59, 223, 79, 132, 139, 119)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__7_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__8;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(18, 67, 155, 167, 151, 71, 146, 196)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__9 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__9_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__11;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_strLitToConstructor___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "nil"};
static const lean_object* l_Lean_Expr_strLitToConstructor___closed__0 = (const lean_object*)&l_Lean_Expr_strLitToConstructor___closed__0_value;
static const lean_ctor_object l_Lean_Expr_strLitToConstructor___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_Lean_Expr_strLitToConstructor___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_strLitToConstructor___closed__1_value_aux_0),((lean_object*)&l_Lean_Expr_strLitToConstructor___closed__0_value),LEAN_SCALAR_PTR_LITERAL(90, 150, 134, 113, 145, 38, 173, 251)}};
static const lean_object* l_Lean_Expr_strLitToConstructor___closed__1 = (const lean_object*)&l_Lean_Expr_strLitToConstructor___closed__1_value;
static lean_once_cell_t l_Lean_Expr_strLitToConstructor___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_strLitToConstructor___closed__2;
static lean_once_cell_t l_Lean_Expr_strLitToConstructor___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_strLitToConstructor___closed__3;
static const lean_string_object l_Lean_Expr_strLitToConstructor___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "String"};
static const lean_object* l_Lean_Expr_strLitToConstructor___closed__4 = (const lean_object*)&l_Lean_Expr_strLitToConstructor___closed__4_value;
static const lean_string_object l_Lean_Expr_strLitToConstructor___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ofList"};
static const lean_object* l_Lean_Expr_strLitToConstructor___closed__5 = (const lean_object*)&l_Lean_Expr_strLitToConstructor___closed__5_value;
static const lean_ctor_object l_Lean_Expr_strLitToConstructor___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_strLitToConstructor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_ctor_object l_Lean_Expr_strLitToConstructor___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Expr_strLitToConstructor___closed__6_value_aux_0),((lean_object*)&l_Lean_Expr_strLitToConstructor___closed__5_value),LEAN_SCALAR_PTR_LITERAL(118, 246, 177, 142, 179, 9, 199, 233)}};
static const lean_object* l_Lean_Expr_strLitToConstructor___closed__6 = (const lean_object*)&l_Lean_Expr_strLitToConstructor___closed__6_value;
static lean_once_cell_t l_Lean_Expr_strLitToConstructor___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_strLitToConstructor___closed__7;
LEAN_EXPORT lean_object* l_Lean_Expr_strLitToConstructor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_toConstructor(lean_object*);
static const lean_ctor_object l_Lean_Literal_typeName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_natZero___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Literal_typeName___closed__0 = (const lean_object*)&l_Lean_Literal_typeName___closed__0_value;
static const lean_ctor_object l_Lean_Literal_typeName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_strLitToConstructor___closed__4_value),LEAN_SCALAR_PTR_LITERAL(6, 130, 56, 8, 41, 104, 134, 43)}};
static const lean_object* l_Lean_Literal_typeName___closed__1 = (const lean_object*)&l_Lean_Literal_typeName___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Literal_typeName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Literal_typeName___boxed(lean_object*);
static lean_object* _init_l_Lean_Expr_prop___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Expr_sort___override(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Lean_Expr_prop(void){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_obj_once(&l_Lean_Expr_prop___closed__0, &l_Lean_Expr_prop___closed__0_once, _init_l_Lean_Expr_prop___closed__0);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_arrow(lean_object* v_d_7_, lean_object* v_b_8_){
_start:
{
lean_object* v___x_9_; uint8_t v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l_Lean_Expr_arrow___closed__1));
v___x_10_ = 0;
v___x_11_ = l_Lean_Expr_forallE___override(v___x_9_, v_d_7_, v_b_8_, v___x_10_);
return v___x_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_lam0(lean_object* v_ty_15_, lean_object* v_e_16_){
_start:
{
lean_object* v___x_17_; uint8_t v___x_18_; lean_object* v___x_19_; 
v___x_17_ = ((lean_object*)(l_Lean_Expr_lam0___closed__1));
v___x_18_ = 0;
v___x_19_ = l_Lean_Expr_lam___override(v___x_17_, v_ty_15_, v_e_16_, v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cacheT___redArg___lam__0(lean_object* v_result_20_, lean_object* v_toPure_21_, lean_object* v_____x_22_){
_start:
{
lean_object* v_snd_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_31_; 
v_snd_23_ = lean_ctor_get(v_____x_22_, 1);
v_isSharedCheck_31_ = !lean_is_exclusive(v_____x_22_);
if (v_isSharedCheck_31_ == 0)
{
lean_object* v_unused_32_; 
v_unused_32_ = lean_ctor_get(v_____x_22_, 0);
lean_dec(v_unused_32_);
v___x_25_ = v_____x_22_;
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_snd_23_);
lean_dec(v_____x_22_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_31_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
lean_object* v___x_28_; 
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 0, v_result_20_);
v___x_28_ = v___x_25_;
goto v_reusejp_27_;
}
else
{
lean_object* v_reuseFailAlloc_30_; 
v_reuseFailAlloc_30_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_30_, 0, v_result_20_);
lean_ctor_set(v_reuseFailAlloc_30_, 1, v_snd_23_);
v___x_28_ = v_reuseFailAlloc_30_;
goto v_reusejp_27_;
}
v_reusejp_27_:
{
lean_object* v___x_29_; 
v___x_29_ = lean_apply_2(v_toPure_21_, lean_box(0), v___x_28_);
return v___x_29_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cacheT___redArg(lean_object* v_inst_35_, lean_object* v_key_36_, lean_object* v_result_37_, lean_object* v_a_38_){
_start:
{
lean_object* v_toApplicative_39_; lean_object* v_toBind_40_; lean_object* v___x_42_; uint8_t v_isShared_43_; uint8_t v_isSharedCheck_55_; 
v_toApplicative_39_ = lean_ctor_get(v_inst_35_, 0);
v_toBind_40_ = lean_ctor_get(v_inst_35_, 1);
v_isSharedCheck_55_ = !lean_is_exclusive(v_inst_35_);
if (v_isSharedCheck_55_ == 0)
{
v___x_42_ = v_inst_35_;
v_isShared_43_ = v_isSharedCheck_55_;
goto v_resetjp_41_;
}
else
{
lean_inc(v_toBind_40_);
lean_inc(v_toApplicative_39_);
lean_dec(v_inst_35_);
v___x_42_ = lean_box(0);
v_isShared_43_ = v_isSharedCheck_55_;
goto v_resetjp_41_;
}
v_resetjp_41_:
{
lean_object* v_toPure_44_; lean_object* v___f_45_; lean_object* v___x_46_; lean_object* v___f_47_; lean_object* v___f_48_; lean_object* v___x_49_; lean_object* v___x_51_; 
v_toPure_44_ = lean_ctor_get(v_toApplicative_39_, 1);
lean_inc_n(v_toPure_44_, 2);
lean_dec_ref(v_toApplicative_39_);
lean_inc_ref(v_result_37_);
v___f_45_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_45_, 0, v_result_37_);
lean_closure_set(v___f_45_, 1, v_toPure_44_);
v___x_46_ = lean_box(0);
v___f_47_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_48_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_49_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_47_, v___f_48_, v_a_38_, v_key_36_, v_result_37_);
if (v_isShared_43_ == 0)
{
lean_ctor_set(v___x_42_, 1, v___x_49_);
lean_ctor_set(v___x_42_, 0, v___x_46_);
v___x_51_ = v___x_42_;
goto v_reusejp_50_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_46_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v___x_49_);
v___x_51_ = v_reuseFailAlloc_54_;
goto v_reusejp_50_;
}
v_reusejp_50_:
{
lean_object* v___x_52_; lean_object* v___x_53_; 
v___x_52_ = lean_apply_2(v_toPure_44_, lean_box(0), v___x_51_);
v___x_53_ = lean_apply_4(v_toBind_40_, lean_box(0), lean_box(0), v___x_52_, v___f_45_);
return v___x_53_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_cacheT(lean_object* v_m_56_, lean_object* v_inst_57_, lean_object* v_key_58_, lean_object* v_result_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_toApplicative_61_; lean_object* v_toBind_62_; lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_77_; 
v_toApplicative_61_ = lean_ctor_get(v_inst_57_, 0);
v_toBind_62_ = lean_ctor_get(v_inst_57_, 1);
v_isSharedCheck_77_ = !lean_is_exclusive(v_inst_57_);
if (v_isSharedCheck_77_ == 0)
{
v___x_64_ = v_inst_57_;
v_isShared_65_ = v_isSharedCheck_77_;
goto v_resetjp_63_;
}
else
{
lean_inc(v_toBind_62_);
lean_inc(v_toApplicative_61_);
lean_dec(v_inst_57_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_77_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v_toPure_66_; lean_object* v___f_67_; lean_object* v___x_68_; lean_object* v___f_69_; lean_object* v___f_70_; lean_object* v___x_71_; lean_object* v___x_73_; 
v_toPure_66_ = lean_ctor_get(v_toApplicative_61_, 1);
lean_inc_n(v_toPure_66_, 2);
lean_dec_ref(v_toApplicative_61_);
lean_inc_ref(v_result_59_);
v___f_67_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_67_, 0, v_result_59_);
lean_closure_set(v___f_67_, 1, v_toPure_66_);
v___x_68_ = lean_box(0);
v___f_69_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_70_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_71_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_69_, v___f_70_, v_a_60_, v_key_58_, v_result_59_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 1, v___x_71_);
lean_ctor_set(v___x_64_, 0, v___x_68_);
v___x_73_ = v___x_64_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_76_; 
v_reuseFailAlloc_76_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_76_, 0, v___x_68_);
lean_ctor_set(v_reuseFailAlloc_76_, 1, v___x_71_);
v___x_73_ = v_reuseFailAlloc_76_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_apply_2(v_toPure_66_, lean_box(0), v___x_73_);
v___x_75_ = lean_apply_4(v_toBind_62_, lean_box(0), lean_box(0), v___x_74_, v___f_67_);
return v___x_75_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0(lean_object* v___y_78_, lean_object* v_toPure_79_, lean_object* v_____x_80_){
_start:
{
lean_object* v_snd_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_89_; 
v_snd_81_ = lean_ctor_get(v_____x_80_, 1);
v_isSharedCheck_89_ = !lean_is_exclusive(v_____x_80_);
if (v_isSharedCheck_89_ == 0)
{
lean_object* v_unused_90_; 
v_unused_90_ = lean_ctor_get(v_____x_80_, 0);
lean_dec(v_unused_90_);
v___x_83_ = v_____x_80_;
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_snd_81_);
lean_dec(v_____x_80_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_89_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v___y_78_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_88_; 
v_reuseFailAlloc_88_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_88_, 0, v___y_78_);
lean_ctor_set(v_reuseFailAlloc_88_, 1, v_snd_81_);
v___x_86_ = v_reuseFailAlloc_88_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; 
v___x_87_ = lean_apply_2(v_toPure_79_, lean_box(0), v___x_86_);
return v___x_87_;
}
}
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v___x_94_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__2));
v___x_95_ = lean_unsigned_to_nat(17u);
v___x_96_ = lean_unsigned_to_nat(1876u);
v___x_97_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__1));
v___x_98_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__0));
v___x_99_ = l_mkPanicMessageWithDecl(v___x_98_, v___x_97_, v___x_96_, v___x_95_, v___x_94_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1(lean_object* v_toPure_100_, lean_object* v_e_101_, lean_object* v_toBind_102_, lean_object* v_____x_103_){
_start:
{
lean_object* v_fst_104_; lean_object* v_snd_105_; lean_object* v___x_107_; uint8_t v_isShared_108_; uint8_t v_isSharedCheck_130_; 
v_fst_104_ = lean_ctor_get(v_____x_103_, 0);
v_snd_105_ = lean_ctor_get(v_____x_103_, 1);
v_isSharedCheck_130_ = !lean_is_exclusive(v_____x_103_);
if (v_isSharedCheck_130_ == 0)
{
v___x_107_ = v_____x_103_;
v_isShared_108_ = v_isSharedCheck_130_;
goto v_resetjp_106_;
}
else
{
lean_inc(v_snd_105_);
lean_inc(v_fst_104_);
lean_dec(v_____x_103_);
v___x_107_ = lean_box(0);
v_isShared_108_ = v_isSharedCheck_130_;
goto v_resetjp_106_;
}
v_resetjp_106_:
{
lean_object* v___y_110_; 
if (lean_obj_tag(v_e_101_) == 10)
{
lean_object* v_data_121_; lean_object* v_expr_122_; size_t v___x_123_; size_t v___x_124_; uint8_t v___x_125_; 
v_data_121_ = lean_ctor_get(v_e_101_, 0);
v_expr_122_ = lean_ctor_get(v_e_101_, 1);
v___x_123_ = lean_ptr_addr(v_expr_122_);
v___x_124_ = lean_ptr_addr(v_fst_104_);
v___x_125_ = lean_usize_dec_eq(v___x_123_, v___x_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; 
lean_inc(v_data_121_);
v___x_126_ = l_Lean_Expr_mdata___override(v_data_121_, v_fst_104_);
v___y_110_ = v___x_126_;
goto v___jp_109_;
}
else
{
lean_dec(v_fst_104_);
lean_inc_ref(v_e_101_);
v___y_110_ = v_e_101_;
goto v___jp_109_;
}
}
else
{
lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_fst_104_);
v___x_127_ = l_Lean_instInhabitedExpr;
v___x_128_ = lean_obj_once(&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3, &l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3_once, _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3);
v___x_129_ = l_panic___redArg(v___x_127_, v___x_128_);
v___y_110_ = v___x_129_;
goto v___jp_109_;
}
v___jp_109_:
{
lean_object* v___f_111_; lean_object* v___x_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_117_; 
lean_inc(v_toPure_100_);
lean_inc_ref(v___y_110_);
v___f_111_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_111_, 0, v___y_110_);
lean_closure_set(v___f_111_, 1, v_toPure_100_);
v___x_112_ = lean_box(0);
v___f_113_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_114_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_115_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_113_, v___f_114_, v_snd_105_, v_e_101_, v___y_110_);
if (v_isShared_108_ == 0)
{
lean_ctor_set(v___x_107_, 1, v___x_115_);
lean_ctor_set(v___x_107_, 0, v___x_112_);
v___x_117_ = v___x_107_;
goto v_reusejp_116_;
}
else
{
lean_object* v_reuseFailAlloc_120_; 
v_reuseFailAlloc_120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_120_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_120_, 1, v___x_115_);
v___x_117_ = v_reuseFailAlloc_120_;
goto v_reusejp_116_;
}
v_reusejp_116_:
{
lean_object* v___x_118_; lean_object* v___x_119_; 
v___x_118_ = lean_apply_2(v_toPure_100_, lean_box(0), v___x_117_);
v___x_119_ = lean_apply_4(v_toBind_102_, lean_box(0), lean_box(0), v___x_118_, v___f_111_);
return v___x_119_;
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2(void){
_start:
{
lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_133_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__1));
v___x_134_ = lean_unsigned_to_nat(18u);
v___x_135_ = lean_unsigned_to_nat(1887u);
v___x_136_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__0));
v___x_137_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__0));
v___x_138_ = l_mkPanicMessageWithDecl(v___x_137_, v___x_136_, v___x_135_, v___x_134_, v___x_133_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3(lean_object* v_toPure_139_, lean_object* v_e_140_, lean_object* v_toBind_141_, lean_object* v_____x_142_){
_start:
{
lean_object* v_fst_143_; lean_object* v_snd_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_170_; 
v_fst_143_ = lean_ctor_get(v_____x_142_, 0);
v_snd_144_ = lean_ctor_get(v_____x_142_, 1);
v_isSharedCheck_170_ = !lean_is_exclusive(v_____x_142_);
if (v_isSharedCheck_170_ == 0)
{
v___x_146_ = v_____x_142_;
v_isShared_147_ = v_isSharedCheck_170_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snd_144_);
lean_inc(v_fst_143_);
lean_dec(v_____x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_170_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___y_149_; 
if (lean_obj_tag(v_e_140_) == 11)
{
lean_object* v_typeName_160_; lean_object* v_idx_161_; lean_object* v_struct_162_; size_t v___x_163_; size_t v___x_164_; uint8_t v___x_165_; 
v_typeName_160_ = lean_ctor_get(v_e_140_, 0);
v_idx_161_ = lean_ctor_get(v_e_140_, 1);
v_struct_162_ = lean_ctor_get(v_e_140_, 2);
v___x_163_ = lean_ptr_addr(v_struct_162_);
v___x_164_ = lean_ptr_addr(v_fst_143_);
v___x_165_ = lean_usize_dec_eq(v___x_163_, v___x_164_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; 
lean_inc(v_idx_161_);
lean_inc(v_typeName_160_);
v___x_166_ = l_Lean_Expr_proj___override(v_typeName_160_, v_idx_161_, v_fst_143_);
v___y_149_ = v___x_166_;
goto v___jp_148_;
}
else
{
lean_dec(v_fst_143_);
lean_inc_ref(v_e_140_);
v___y_149_ = v_e_140_;
goto v___jp_148_;
}
}
else
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_fst_143_);
v___x_167_ = l_Lean_instInhabitedExpr;
v___x_168_ = lean_obj_once(&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2, &l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2_once, _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2);
v___x_169_ = l_panic___redArg(v___x_167_, v___x_168_);
v___y_149_ = v___x_169_;
goto v___jp_148_;
}
v___jp_148_:
{
lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___f_152_; lean_object* v___f_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
lean_inc(v_toPure_139_);
lean_inc_ref(v___y_149_);
v___f_150_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_150_, 0, v___y_149_);
lean_closure_set(v___f_150_, 1, v_toPure_139_);
v___x_151_ = lean_box(0);
v___f_152_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_153_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_154_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_152_, v___f_153_, v_snd_144_, v_e_140_, v___y_149_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_154_);
lean_ctor_set(v___x_146_, 0, v___x_151_);
v___x_156_ = v___x_146_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_151_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_154_);
v___x_156_ = v_reuseFailAlloc_159_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_apply_2(v_toPure_139_, lean_box(0), v___x_156_);
v___x_158_ = lean_apply_4(v_toBind_141_, lean_box(0), lean_box(0), v___x_157_, v___f_150_);
return v___x_158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__2(lean_object* v_toPure_171_, lean_object* v_result_172_, lean_object* v___y_173_){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_174_, 0, v_result_172_);
lean_ctor_set(v___x_174_, 1, v___y_173_);
v___x_175_ = lean_apply_2(v_toPure_171_, lean_box(0), v___x_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__5(lean_object* v_toPure_176_, lean_object* v_e_177_, lean_object* v_toBind_178_, lean_object* v_binderName_179_, lean_object* v_fst_180_, uint8_t v_binderInfo_181_, lean_object* v_binderType_182_, lean_object* v_body_183_, lean_object* v_____x_184_){
_start:
{
lean_object* v_fst_185_; lean_object* v_snd_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_213_; 
v_fst_185_ = lean_ctor_get(v_____x_184_, 0);
v_snd_186_ = lean_ctor_get(v_____x_184_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_____x_184_);
if (v_isSharedCheck_213_ == 0)
{
v___x_188_ = v_____x_184_;
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_snd_186_);
lean_inc(v_fst_185_);
lean_dec(v_____x_184_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_213_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___y_191_; uint8_t v___y_203_; size_t v___x_207_; size_t v___x_208_; uint8_t v___x_209_; 
v___x_207_ = lean_ptr_addr(v_binderType_182_);
v___x_208_ = lean_ptr_addr(v_fst_180_);
v___x_209_ = lean_usize_dec_eq(v___x_207_, v___x_208_);
if (v___x_209_ == 0)
{
v___y_203_ = v___x_209_;
goto v___jp_202_;
}
else
{
size_t v___x_210_; size_t v___x_211_; uint8_t v___x_212_; 
v___x_210_ = lean_ptr_addr(v_body_183_);
v___x_211_ = lean_ptr_addr(v_fst_185_);
v___x_212_ = lean_usize_dec_eq(v___x_210_, v___x_211_);
v___y_203_ = v___x_212_;
goto v___jp_202_;
}
v___jp_190_:
{
lean_object* v___f_192_; lean_object* v___x_193_; lean_object* v___f_194_; lean_object* v___f_195_; lean_object* v___x_196_; lean_object* v___x_198_; 
lean_inc(v_toPure_176_);
lean_inc_ref(v___y_191_);
v___f_192_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_192_, 0, v___y_191_);
lean_closure_set(v___f_192_, 1, v_toPure_176_);
v___x_193_ = lean_box(0);
v___f_194_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_195_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_196_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_194_, v___f_195_, v_snd_186_, v_e_177_, v___y_191_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_196_);
lean_ctor_set(v___x_188_, 0, v___x_193_);
v___x_198_ = v___x_188_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v___x_196_);
v___x_198_ = v_reuseFailAlloc_201_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_apply_2(v_toPure_176_, lean_box(0), v___x_198_);
v___x_200_ = lean_apply_4(v_toBind_178_, lean_box(0), lean_box(0), v___x_199_, v___f_192_);
return v___x_200_;
}
}
v___jp_202_:
{
if (v___y_203_ == 0)
{
lean_object* v___x_204_; 
v___x_204_ = l_Lean_Expr_forallE___override(v_binderName_179_, v_fst_180_, v_fst_185_, v_binderInfo_181_);
v___y_191_ = v___x_204_;
goto v___jp_190_;
}
else
{
uint8_t v___x_205_; 
v___x_205_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_181_, v_binderInfo_181_);
if (v___x_205_ == 0)
{
lean_object* v___x_206_; 
v___x_206_ = l_Lean_Expr_forallE___override(v_binderName_179_, v_fst_180_, v_fst_185_, v_binderInfo_181_);
v___y_191_ = v___x_206_;
goto v___jp_190_;
}
else
{
lean_dec(v_fst_185_);
lean_dec_ref(v_fst_180_);
lean_dec(v_binderName_179_);
lean_inc_ref(v_e_177_);
v___y_191_ = v_e_177_;
goto v___jp_190_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__5___boxed(lean_object* v_toPure_214_, lean_object* v_e_215_, lean_object* v_toBind_216_, lean_object* v_binderName_217_, lean_object* v_fst_218_, lean_object* v_binderInfo_219_, lean_object* v_binderType_220_, lean_object* v_body_221_, lean_object* v_____x_222_){
_start:
{
uint8_t v_binderInfo_3806__boxed_223_; lean_object* v_res_224_; 
v_binderInfo_3806__boxed_223_ = lean_unbox(v_binderInfo_219_);
v_res_224_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__5(v_toPure_214_, v_e_215_, v_toBind_216_, v_binderName_217_, v_fst_218_, v_binderInfo_3806__boxed_223_, v_binderType_220_, v_body_221_, v_____x_222_);
lean_dec_ref(v_body_221_);
lean_dec_ref(v_binderType_220_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__9(lean_object* v_toPure_225_, lean_object* v_e_226_, lean_object* v_toBind_227_, lean_object* v_declName_228_, lean_object* v_fst_229_, lean_object* v_fst_230_, uint8_t v_nondep_231_, lean_object* v_body_232_, lean_object* v_type_233_, lean_object* v_value_234_, lean_object* v_____x_235_){
_start:
{
lean_object* v_fst_236_; lean_object* v_snd_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_266_; 
v_fst_236_ = lean_ctor_get(v_____x_235_, 0);
v_snd_237_ = lean_ctor_get(v_____x_235_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_____x_235_);
if (v_isSharedCheck_266_ == 0)
{
v___x_239_ = v_____x_235_;
v_isShared_240_ = v_isSharedCheck_266_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_snd_237_);
lean_inc(v_fst_236_);
lean_dec(v_____x_235_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_266_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___y_242_; uint8_t v___y_254_; size_t v___x_260_; size_t v___x_261_; uint8_t v___x_262_; 
v___x_260_ = lean_ptr_addr(v_type_233_);
v___x_261_ = lean_ptr_addr(v_fst_229_);
v___x_262_ = lean_usize_dec_eq(v___x_260_, v___x_261_);
if (v___x_262_ == 0)
{
v___y_254_ = v___x_262_;
goto v___jp_253_;
}
else
{
size_t v___x_263_; size_t v___x_264_; uint8_t v___x_265_; 
v___x_263_ = lean_ptr_addr(v_value_234_);
v___x_264_ = lean_ptr_addr(v_fst_230_);
v___x_265_ = lean_usize_dec_eq(v___x_263_, v___x_264_);
v___y_254_ = v___x_265_;
goto v___jp_253_;
}
v___jp_241_:
{
lean_object* v___f_243_; lean_object* v___x_244_; lean_object* v___f_245_; lean_object* v___f_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
lean_inc(v_toPure_225_);
lean_inc_ref(v___y_242_);
v___f_243_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_243_, 0, v___y_242_);
lean_closure_set(v___f_243_, 1, v_toPure_225_);
v___x_244_ = lean_box(0);
v___f_245_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_246_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_247_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_245_, v___f_246_, v_snd_237_, v_e_226_, v___y_242_);
if (v_isShared_240_ == 0)
{
lean_ctor_set(v___x_239_, 1, v___x_247_);
lean_ctor_set(v___x_239_, 0, v___x_244_);
v___x_249_ = v___x_239_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_244_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_252_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_250_ = lean_apply_2(v_toPure_225_, lean_box(0), v___x_249_);
v___x_251_ = lean_apply_4(v_toBind_227_, lean_box(0), lean_box(0), v___x_250_, v___f_243_);
return v___x_251_;
}
}
v___jp_253_:
{
if (v___y_254_ == 0)
{
lean_object* v___x_255_; 
v___x_255_ = l_Lean_Expr_letE___override(v_declName_228_, v_fst_229_, v_fst_230_, v_fst_236_, v_nondep_231_);
v___y_242_ = v___x_255_;
goto v___jp_241_;
}
else
{
size_t v___x_256_; size_t v___x_257_; uint8_t v___x_258_; 
v___x_256_ = lean_ptr_addr(v_body_232_);
v___x_257_ = lean_ptr_addr(v_fst_236_);
v___x_258_ = lean_usize_dec_eq(v___x_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = l_Lean_Expr_letE___override(v_declName_228_, v_fst_229_, v_fst_230_, v_fst_236_, v_nondep_231_);
v___y_242_ = v___x_259_;
goto v___jp_241_;
}
else
{
lean_dec(v_fst_236_);
lean_dec_ref(v_fst_230_);
lean_dec_ref(v_fst_229_);
lean_dec(v_declName_228_);
lean_inc_ref(v_e_226_);
v___y_242_ = v_e_226_;
goto v___jp_241_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__9___boxed(lean_object* v_toPure_267_, lean_object* v_e_268_, lean_object* v_toBind_269_, lean_object* v_declName_270_, lean_object* v_fst_271_, lean_object* v_fst_272_, lean_object* v_nondep_273_, lean_object* v_body_274_, lean_object* v_type_275_, lean_object* v_value_276_, lean_object* v_____x_277_){
_start:
{
uint8_t v_nondep_3885__boxed_278_; lean_object* v_res_279_; 
v_nondep_3885__boxed_278_ = lean_unbox(v_nondep_273_);
v_res_279_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__9(v_toPure_267_, v_e_268_, v_toBind_269_, v_declName_270_, v_fst_271_, v_fst_272_, v_nondep_3885__boxed_278_, v_body_274_, v_type_275_, v_value_276_, v_____x_277_);
lean_dec_ref(v_value_276_);
lean_dec_ref(v_type_275_);
lean_dec_ref(v_body_274_);
return v_res_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__7(lean_object* v_toPure_280_, lean_object* v_e_281_, lean_object* v_toBind_282_, lean_object* v_binderName_283_, lean_object* v_fst_284_, uint8_t v_binderInfo_285_, lean_object* v_binderType_286_, lean_object* v_body_287_, lean_object* v_____x_288_){
_start:
{
lean_object* v_fst_289_; lean_object* v_snd_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_317_; 
v_fst_289_ = lean_ctor_get(v_____x_288_, 0);
v_snd_290_ = lean_ctor_get(v_____x_288_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_____x_288_);
if (v_isSharedCheck_317_ == 0)
{
v___x_292_ = v_____x_288_;
v_isShared_293_ = v_isSharedCheck_317_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_snd_290_);
lean_inc(v_fst_289_);
lean_dec(v_____x_288_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_317_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___y_295_; uint8_t v___y_307_; size_t v___x_311_; size_t v___x_312_; uint8_t v___x_313_; 
v___x_311_ = lean_ptr_addr(v_binderType_286_);
v___x_312_ = lean_ptr_addr(v_fst_284_);
v___x_313_ = lean_usize_dec_eq(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
v___y_307_ = v___x_313_;
goto v___jp_306_;
}
else
{
size_t v___x_314_; size_t v___x_315_; uint8_t v___x_316_; 
v___x_314_ = lean_ptr_addr(v_body_287_);
v___x_315_ = lean_ptr_addr(v_fst_289_);
v___x_316_ = lean_usize_dec_eq(v___x_314_, v___x_315_);
v___y_307_ = v___x_316_;
goto v___jp_306_;
}
v___jp_294_:
{
lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___f_298_; lean_object* v___f_299_; lean_object* v___x_300_; lean_object* v___x_302_; 
lean_inc(v_toPure_280_);
lean_inc_ref(v___y_295_);
v___f_296_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_296_, 0, v___y_295_);
lean_closure_set(v___f_296_, 1, v_toPure_280_);
v___x_297_ = lean_box(0);
v___f_298_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_299_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_300_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_298_, v___f_299_, v_snd_290_, v_e_281_, v___y_295_);
if (v_isShared_293_ == 0)
{
lean_ctor_set(v___x_292_, 1, v___x_300_);
lean_ctor_set(v___x_292_, 0, v___x_297_);
v___x_302_ = v___x_292_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_297_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v___x_300_);
v___x_302_ = v_reuseFailAlloc_305_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_apply_2(v_toPure_280_, lean_box(0), v___x_302_);
v___x_304_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v___x_303_, v___f_296_);
return v___x_304_;
}
}
v___jp_306_:
{
if (v___y_307_ == 0)
{
lean_object* v___x_308_; 
v___x_308_ = l_Lean_Expr_lam___override(v_binderName_283_, v_fst_284_, v_fst_289_, v_binderInfo_285_);
v___y_295_ = v___x_308_;
goto v___jp_294_;
}
else
{
uint8_t v___x_309_; 
v___x_309_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_285_, v_binderInfo_285_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; 
v___x_310_ = l_Lean_Expr_lam___override(v_binderName_283_, v_fst_284_, v_fst_289_, v_binderInfo_285_);
v___y_295_ = v___x_310_;
goto v___jp_294_;
}
else
{
lean_dec(v_fst_289_);
lean_dec_ref(v_fst_284_);
lean_dec(v_binderName_283_);
lean_inc_ref(v_e_281_);
v___y_295_ = v_e_281_;
goto v___jp_294_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__7___boxed(lean_object* v_toPure_318_, lean_object* v_e_319_, lean_object* v_toBind_320_, lean_object* v_binderName_321_, lean_object* v_fst_322_, lean_object* v_binderInfo_323_, lean_object* v_binderType_324_, lean_object* v_body_325_, lean_object* v_____x_326_){
_start:
{
uint8_t v_binderInfo_3972__boxed_327_; lean_object* v_res_328_; 
v_binderInfo_3972__boxed_327_ = lean_unbox(v_binderInfo_323_);
v_res_328_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__7(v_toPure_318_, v_e_319_, v_toBind_320_, v_binderName_321_, v_fst_322_, v_binderInfo_3972__boxed_327_, v_binderType_324_, v_body_325_, v_____x_326_);
lean_dec_ref(v_body_325_);
lean_dec_ref(v_binderType_324_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__12(lean_object* v_toPure_329_, lean_object* v_e_330_, lean_object* v_toBind_331_, lean_object* v_fst_332_, lean_object* v_fn_333_, lean_object* v_arg_334_, lean_object* v_____x_335_){
_start:
{
lean_object* v_fst_336_; lean_object* v_snd_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_362_; 
v_fst_336_ = lean_ctor_get(v_____x_335_, 0);
v_snd_337_ = lean_ctor_get(v_____x_335_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_____x_335_);
if (v_isSharedCheck_362_ == 0)
{
v___x_339_ = v_____x_335_;
v_isShared_340_ = v_isSharedCheck_362_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_snd_337_);
lean_inc(v_fst_336_);
lean_dec(v_____x_335_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_362_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___y_342_; uint8_t v___y_354_; size_t v___x_356_; size_t v___x_357_; uint8_t v___x_358_; 
v___x_356_ = lean_ptr_addr(v_fn_333_);
v___x_357_ = lean_ptr_addr(v_fst_332_);
v___x_358_ = lean_usize_dec_eq(v___x_356_, v___x_357_);
if (v___x_358_ == 0)
{
v___y_354_ = v___x_358_;
goto v___jp_353_;
}
else
{
size_t v___x_359_; size_t v___x_360_; uint8_t v___x_361_; 
v___x_359_ = lean_ptr_addr(v_arg_334_);
v___x_360_ = lean_ptr_addr(v_fst_336_);
v___x_361_ = lean_usize_dec_eq(v___x_359_, v___x_360_);
v___y_354_ = v___x_361_;
goto v___jp_353_;
}
v___jp_341_:
{
lean_object* v___f_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___f_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
lean_inc(v_toPure_329_);
lean_inc_ref(v___y_342_);
v___f_343_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__0), 3, 2);
lean_closure_set(v___f_343_, 0, v___y_342_);
lean_closure_set(v___f_343_, 1, v_toPure_329_);
v___x_344_ = lean_box(0);
v___f_345_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_346_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_347_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_345_, v___f_346_, v_snd_337_, v_e_330_, v___y_342_);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 1, v___x_347_);
lean_ctor_set(v___x_339_, 0, v___x_344_);
v___x_349_ = v___x_339_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v___x_344_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v___x_347_);
v___x_349_ = v_reuseFailAlloc_352_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = lean_apply_2(v_toPure_329_, lean_box(0), v___x_349_);
v___x_351_ = lean_apply_4(v_toBind_331_, lean_box(0), lean_box(0), v___x_350_, v___f_343_);
return v___x_351_;
}
}
v___jp_353_:
{
if (v___y_354_ == 0)
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Expr_app___override(v_fst_332_, v_fst_336_);
v___y_342_ = v___x_355_;
goto v___jp_341_;
}
else
{
lean_dec(v_fst_336_);
lean_dec_ref(v_fst_332_);
lean_inc_ref(v_e_330_);
v___y_342_ = v_e_330_;
goto v___jp_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__12___boxed(lean_object* v_toPure_363_, lean_object* v_e_364_, lean_object* v_toBind_365_, lean_object* v_fst_366_, lean_object* v_fn_367_, lean_object* v_arg_368_, lean_object* v_____x_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__12(v_toPure_363_, v_e_364_, v_toBind_365_, v_fst_366_, v_fn_367_, v_arg_368_, v_____x_369_);
lean_dec_ref(v_arg_368_);
lean_dec_ref(v_fn_367_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__13(lean_object* v_val_371_, lean_object* v_toPure_372_, lean_object* v_____x_373_){
_start:
{
lean_object* v_snd_374_; lean_object* v___x_376_; uint8_t v_isShared_377_; uint8_t v_isSharedCheck_382_; 
v_snd_374_ = lean_ctor_get(v_____x_373_, 1);
v_isSharedCheck_382_ = !lean_is_exclusive(v_____x_373_);
if (v_isSharedCheck_382_ == 0)
{
lean_object* v_unused_383_; 
v_unused_383_ = lean_ctor_get(v_____x_373_, 0);
lean_dec(v_unused_383_);
v___x_376_ = v_____x_373_;
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
else
{
lean_inc(v_snd_374_);
lean_dec(v_____x_373_);
v___x_376_ = lean_box(0);
v_isShared_377_ = v_isSharedCheck_382_;
goto v_resetjp_375_;
}
v_resetjp_375_:
{
lean_object* v___x_379_; 
if (v_isShared_377_ == 0)
{
lean_ctor_set(v___x_376_, 0, v_val_371_);
v___x_379_ = v___x_376_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v_val_371_);
lean_ctor_set(v_reuseFailAlloc_381_, 1, v_snd_374_);
v___x_379_ = v_reuseFailAlloc_381_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
lean_object* v___x_380_; 
v___x_380_ = lean_apply_2(v_toPure_372_, lean_box(0), v___x_379_);
return v___x_380_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__15(lean_object* v_snd_384_, lean_object* v_toPure_385_, lean_object* v_a_386_){
_start:
{
lean_object* v___x_387_; lean_object* v___x_388_; 
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_a_386_);
lean_ctor_set(v___x_387_, 1, v_snd_384_);
v___x_388_ = lean_apply_2(v_toPure_385_, lean_box(0), v___x_387_);
return v___x_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__16(lean_object* v_e_389_, lean_object* v___f_390_, lean_object* v_f_x3f_391_, lean_object* v_toPure_392_, lean_object* v_toBind_393_, lean_object* v___f_394_, lean_object* v_____x_395_){
_start:
{
lean_object* v_fst_396_; lean_object* v_snd_397_; lean_object* v___f_398_; lean_object* v___f_399_; lean_object* v___x_400_; 
v_fst_396_ = lean_ctor_get(v_____x_395_, 0);
lean_inc(v_fst_396_);
v_snd_397_ = lean_ctor_get(v_____x_395_, 1);
lean_inc(v_snd_397_);
lean_dec_ref(v_____x_395_);
v___f_398_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_399_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
lean_inc_ref(v_e_389_);
v___x_400_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___f_398_, v___f_399_, v_fst_396_, v_e_389_);
lean_dec(v_fst_396_);
if (lean_obj_tag(v___x_400_) == 1)
{
lean_object* v_val_401_; lean_object* v___x_402_; 
lean_dec(v___f_394_);
lean_dec(v_toBind_393_);
lean_dec(v_toPure_392_);
lean_dec(v_f_x3f_391_);
lean_dec_ref(v_e_389_);
v_val_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_val_401_);
lean_dec_ref(v___x_400_);
v___x_402_ = lean_apply_2(v___f_390_, v_val_401_, v_snd_397_);
return v___x_402_;
}
else
{
lean_object* v___x_403_; lean_object* v___f_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
lean_dec(v___x_400_);
lean_dec(v___f_390_);
v___x_403_ = lean_apply_1(v_f_x3f_391_, v_e_389_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__15), 3, 2);
lean_closure_set(v___f_404_, 0, v_snd_397_);
lean_closure_set(v___f_404_, 1, v_toPure_392_);
lean_inc(v_toBind_393_);
v___x_405_ = lean_apply_4(v_toBind_393_, lean_box(0), lean_box(0), v___x_403_, v___f_404_);
v___x_406_ = lean_apply_4(v_toBind_393_, lean_box(0), lean_box(0), v___x_405_, v___f_394_);
return v___x_406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__4(lean_object* v_toPure_407_, lean_object* v_e_408_, lean_object* v_toBind_409_, lean_object* v_binderName_410_, uint8_t v_binderInfo_411_, lean_object* v_binderType_412_, lean_object* v_body_413_, lean_object* v_inst_414_, lean_object* v_f_x3f_415_, lean_object* v_____x_416_){
_start:
{
lean_object* v_fst_417_; lean_object* v_snd_418_; lean_object* v___x_419_; lean_object* v___f_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v_fst_417_ = lean_ctor_get(v_____x_416_, 0);
lean_inc(v_fst_417_);
v_snd_418_ = lean_ctor_get(v_____x_416_, 1);
lean_inc(v_snd_418_);
lean_dec_ref(v_____x_416_);
v___x_419_ = lean_box(v_binderInfo_411_);
lean_inc_ref(v_body_413_);
lean_inc(v_toBind_409_);
v___f_420_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__5___boxed), 9, 8);
lean_closure_set(v___f_420_, 0, v_toPure_407_);
lean_closure_set(v___f_420_, 1, v_e_408_);
lean_closure_set(v___f_420_, 2, v_toBind_409_);
lean_closure_set(v___f_420_, 3, v_binderName_410_);
lean_closure_set(v___f_420_, 4, v_fst_417_);
lean_closure_set(v___f_420_, 5, v___x_419_);
lean_closure_set(v___f_420_, 6, v_binderType_412_);
lean_closure_set(v___f_420_, 7, v_body_413_);
v___x_421_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_414_, v_f_x3f_415_, v_body_413_, v_snd_418_);
v___x_422_ = lean_apply_4(v_toBind_409_, lean_box(0), lean_box(0), v___x_421_, v___f_420_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__4___boxed(lean_object* v_toPure_423_, lean_object* v_e_424_, lean_object* v_toBind_425_, lean_object* v_binderName_426_, lean_object* v_binderInfo_427_, lean_object* v_binderType_428_, lean_object* v_body_429_, lean_object* v_inst_430_, lean_object* v_f_x3f_431_, lean_object* v_____x_432_){
_start:
{
uint8_t v_binderInfo_4199__boxed_433_; lean_object* v_res_434_; 
v_binderInfo_4199__boxed_433_ = lean_unbox(v_binderInfo_427_);
v_res_434_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__4(v_toPure_423_, v_e_424_, v_toBind_425_, v_binderName_426_, v_binderInfo_4199__boxed_433_, v_binderType_428_, v_body_429_, v_inst_430_, v_f_x3f_431_, v_____x_432_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__6(lean_object* v_toPure_435_, lean_object* v_e_436_, lean_object* v_toBind_437_, lean_object* v_binderName_438_, uint8_t v_binderInfo_439_, lean_object* v_binderType_440_, lean_object* v_body_441_, lean_object* v_inst_442_, lean_object* v_f_x3f_443_, lean_object* v_____x_444_){
_start:
{
lean_object* v_fst_445_; lean_object* v_snd_446_; lean_object* v___x_447_; lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_fst_445_ = lean_ctor_get(v_____x_444_, 0);
lean_inc(v_fst_445_);
v_snd_446_ = lean_ctor_get(v_____x_444_, 1);
lean_inc(v_snd_446_);
lean_dec_ref(v_____x_444_);
v___x_447_ = lean_box(v_binderInfo_439_);
lean_inc_ref(v_body_441_);
lean_inc(v_toBind_437_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__7___boxed), 9, 8);
lean_closure_set(v___f_448_, 0, v_toPure_435_);
lean_closure_set(v___f_448_, 1, v_e_436_);
lean_closure_set(v___f_448_, 2, v_toBind_437_);
lean_closure_set(v___f_448_, 3, v_binderName_438_);
lean_closure_set(v___f_448_, 4, v_fst_445_);
lean_closure_set(v___f_448_, 5, v___x_447_);
lean_closure_set(v___f_448_, 6, v_binderType_440_);
lean_closure_set(v___f_448_, 7, v_body_441_);
v___x_449_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_442_, v_f_x3f_443_, v_body_441_, v_snd_446_);
v___x_450_ = lean_apply_4(v_toBind_437_, lean_box(0), lean_box(0), v___x_449_, v___f_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__6___boxed(lean_object* v_toPure_451_, lean_object* v_e_452_, lean_object* v_toBind_453_, lean_object* v_binderName_454_, lean_object* v_binderInfo_455_, lean_object* v_binderType_456_, lean_object* v_body_457_, lean_object* v_inst_458_, lean_object* v_f_x3f_459_, lean_object* v_____x_460_){
_start:
{
uint8_t v_binderInfo_4210__boxed_461_; lean_object* v_res_462_; 
v_binderInfo_4210__boxed_461_ = lean_unbox(v_binderInfo_455_);
v_res_462_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__6(v_toPure_451_, v_e_452_, v_toBind_453_, v_binderName_454_, v_binderInfo_4210__boxed_461_, v_binderType_456_, v_body_457_, v_inst_458_, v_f_x3f_459_, v_____x_460_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__10___boxed(lean_object* v_toPure_463_, lean_object* v_e_464_, lean_object* v_toBind_465_, lean_object* v_declName_466_, lean_object* v_nondep_467_, lean_object* v_body_468_, lean_object* v_type_469_, lean_object* v_value_470_, lean_object* v_inst_471_, lean_object* v_f_x3f_472_, lean_object* v_____x_473_){
_start:
{
uint8_t v_nondep_4178__boxed_474_; lean_object* v_res_475_; 
v_nondep_4178__boxed_474_ = lean_unbox(v_nondep_467_);
v_res_475_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__10(v_toPure_463_, v_e_464_, v_toBind_465_, v_declName_466_, v_nondep_4178__boxed_474_, v_body_468_, v_type_469_, v_value_470_, v_inst_471_, v_f_x3f_472_, v_____x_473_);
return v_res_475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__11(lean_object* v_toPure_476_, lean_object* v_e_477_, lean_object* v_toBind_478_, lean_object* v_fn_479_, lean_object* v_arg_480_, lean_object* v_inst_481_, lean_object* v_f_x3f_482_, lean_object* v_____x_483_){
_start:
{
lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v___f_486_; lean_object* v___x_487_; lean_object* v___x_488_; 
v_fst_484_ = lean_ctor_get(v_____x_483_, 0);
lean_inc(v_fst_484_);
v_snd_485_ = lean_ctor_get(v_____x_483_, 1);
lean_inc(v_snd_485_);
lean_dec_ref(v_____x_483_);
lean_inc_ref(v_arg_480_);
lean_inc(v_toBind_478_);
v___f_486_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__12___boxed), 7, 6);
lean_closure_set(v___f_486_, 0, v_toPure_476_);
lean_closure_set(v___f_486_, 1, v_e_477_);
lean_closure_set(v___f_486_, 2, v_toBind_478_);
lean_closure_set(v___f_486_, 3, v_fst_484_);
lean_closure_set(v___f_486_, 4, v_fn_479_);
lean_closure_set(v___f_486_, 5, v_arg_480_);
v___x_487_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_481_, v_f_x3f_482_, v_arg_480_, v_snd_485_);
v___x_488_ = lean_apply_4(v_toBind_478_, lean_box(0), lean_box(0), v___x_487_, v___f_486_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__14(lean_object* v_e_489_, lean_object* v_toPure_490_, lean_object* v_toBind_491_, lean_object* v_inst_492_, lean_object* v_f_x3f_493_, lean_object* v___f_494_, lean_object* v___f_495_, lean_object* v___f_496_, lean_object* v_____x_497_){
_start:
{
lean_object* v_fst_498_; 
v_fst_498_ = lean_ctor_get(v_____x_497_, 0);
if (lean_obj_tag(v_fst_498_) == 0)
{
switch(lean_obj_tag(v_e_489_))
{
case 7:
{
lean_object* v_snd_499_; lean_object* v_binderName_500_; lean_object* v_binderType_501_; lean_object* v_body_502_; uint8_t v_binderInfo_503_; lean_object* v___x_504_; lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v___f_496_);
lean_dec(v___f_495_);
lean_dec(v___f_494_);
v_snd_499_ = lean_ctor_get(v_____x_497_, 1);
lean_inc(v_snd_499_);
lean_dec_ref(v_____x_497_);
v_binderName_500_ = lean_ctor_get(v_e_489_, 0);
lean_inc(v_binderName_500_);
v_binderType_501_ = lean_ctor_get(v_e_489_, 1);
lean_inc_ref_n(v_binderType_501_, 2);
v_body_502_ = lean_ctor_get(v_e_489_, 2);
lean_inc_ref(v_body_502_);
v_binderInfo_503_ = lean_ctor_get_uint8(v_e_489_, sizeof(void*)*3 + 8);
v___x_504_ = lean_box(v_binderInfo_503_);
lean_inc(v_f_x3f_493_);
lean_inc_ref(v_inst_492_);
lean_inc(v_toBind_491_);
v___f_505_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__4___boxed), 10, 9);
lean_closure_set(v___f_505_, 0, v_toPure_490_);
lean_closure_set(v___f_505_, 1, v_e_489_);
lean_closure_set(v___f_505_, 2, v_toBind_491_);
lean_closure_set(v___f_505_, 3, v_binderName_500_);
lean_closure_set(v___f_505_, 4, v___x_504_);
lean_closure_set(v___f_505_, 5, v_binderType_501_);
lean_closure_set(v___f_505_, 6, v_body_502_);
lean_closure_set(v___f_505_, 7, v_inst_492_);
lean_closure_set(v___f_505_, 8, v_f_x3f_493_);
v___x_506_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_492_, v_f_x3f_493_, v_binderType_501_, v_snd_499_);
v___x_507_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_506_, v___f_505_);
return v___x_507_;
}
case 6:
{
lean_object* v_snd_508_; lean_object* v_binderName_509_; lean_object* v_binderType_510_; lean_object* v_body_511_; uint8_t v_binderInfo_512_; lean_object* v___x_513_; lean_object* v___f_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_dec(v___f_496_);
lean_dec(v___f_495_);
lean_dec(v___f_494_);
v_snd_508_ = lean_ctor_get(v_____x_497_, 1);
lean_inc(v_snd_508_);
lean_dec_ref(v_____x_497_);
v_binderName_509_ = lean_ctor_get(v_e_489_, 0);
lean_inc(v_binderName_509_);
v_binderType_510_ = lean_ctor_get(v_e_489_, 1);
lean_inc_ref_n(v_binderType_510_, 2);
v_body_511_ = lean_ctor_get(v_e_489_, 2);
lean_inc_ref(v_body_511_);
v_binderInfo_512_ = lean_ctor_get_uint8(v_e_489_, sizeof(void*)*3 + 8);
v___x_513_ = lean_box(v_binderInfo_512_);
lean_inc(v_f_x3f_493_);
lean_inc_ref(v_inst_492_);
lean_inc(v_toBind_491_);
v___f_514_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_514_, 0, v_toPure_490_);
lean_closure_set(v___f_514_, 1, v_e_489_);
lean_closure_set(v___f_514_, 2, v_toBind_491_);
lean_closure_set(v___f_514_, 3, v_binderName_509_);
lean_closure_set(v___f_514_, 4, v___x_513_);
lean_closure_set(v___f_514_, 5, v_binderType_510_);
lean_closure_set(v___f_514_, 6, v_body_511_);
lean_closure_set(v___f_514_, 7, v_inst_492_);
lean_closure_set(v___f_514_, 8, v_f_x3f_493_);
v___x_515_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_492_, v_f_x3f_493_, v_binderType_510_, v_snd_508_);
v___x_516_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_515_, v___f_514_);
return v___x_516_;
}
case 10:
{
lean_object* v_snd_517_; lean_object* v_expr_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
lean_dec(v___f_496_);
lean_dec(v___f_495_);
lean_dec(v_toPure_490_);
v_snd_517_ = lean_ctor_get(v_____x_497_, 1);
lean_inc(v_snd_517_);
lean_dec_ref(v_____x_497_);
v_expr_518_ = lean_ctor_get(v_e_489_, 1);
lean_inc_ref(v_expr_518_);
lean_dec_ref(v_e_489_);
v___x_519_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_492_, v_f_x3f_493_, v_expr_518_, v_snd_517_);
v___x_520_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_519_, v___f_494_);
return v___x_520_;
}
case 8:
{
lean_object* v_snd_521_; lean_object* v_declName_522_; lean_object* v_type_523_; lean_object* v_value_524_; lean_object* v_body_525_; uint8_t v_nondep_526_; lean_object* v___x_527_; lean_object* v___f_528_; lean_object* v___x_529_; lean_object* v___x_530_; 
lean_dec(v___f_496_);
lean_dec(v___f_495_);
lean_dec(v___f_494_);
v_snd_521_ = lean_ctor_get(v_____x_497_, 1);
lean_inc(v_snd_521_);
lean_dec_ref(v_____x_497_);
v_declName_522_ = lean_ctor_get(v_e_489_, 0);
lean_inc(v_declName_522_);
v_type_523_ = lean_ctor_get(v_e_489_, 1);
lean_inc_ref_n(v_type_523_, 2);
v_value_524_ = lean_ctor_get(v_e_489_, 2);
lean_inc_ref(v_value_524_);
v_body_525_ = lean_ctor_get(v_e_489_, 3);
lean_inc_ref(v_body_525_);
v_nondep_526_ = lean_ctor_get_uint8(v_e_489_, sizeof(void*)*4 + 8);
v___x_527_ = lean_box(v_nondep_526_);
lean_inc(v_f_x3f_493_);
lean_inc_ref(v_inst_492_);
lean_inc(v_toBind_491_);
v___f_528_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__10___boxed), 11, 10);
lean_closure_set(v___f_528_, 0, v_toPure_490_);
lean_closure_set(v___f_528_, 1, v_e_489_);
lean_closure_set(v___f_528_, 2, v_toBind_491_);
lean_closure_set(v___f_528_, 3, v_declName_522_);
lean_closure_set(v___f_528_, 4, v___x_527_);
lean_closure_set(v___f_528_, 5, v_body_525_);
lean_closure_set(v___f_528_, 6, v_type_523_);
lean_closure_set(v___f_528_, 7, v_value_524_);
lean_closure_set(v___f_528_, 8, v_inst_492_);
lean_closure_set(v___f_528_, 9, v_f_x3f_493_);
v___x_529_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_492_, v_f_x3f_493_, v_type_523_, v_snd_521_);
v___x_530_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_529_, v___f_528_);
return v___x_530_;
}
case 5:
{
lean_object* v_snd_531_; lean_object* v_fn_532_; lean_object* v_arg_533_; lean_object* v___f_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
lean_dec(v___f_496_);
lean_dec(v___f_495_);
lean_dec(v___f_494_);
v_snd_531_ = lean_ctor_get(v_____x_497_, 1);
lean_inc(v_snd_531_);
lean_dec_ref(v_____x_497_);
v_fn_532_ = lean_ctor_get(v_e_489_, 0);
lean_inc_ref_n(v_fn_532_, 2);
v_arg_533_ = lean_ctor_get(v_e_489_, 1);
lean_inc_ref(v_arg_533_);
lean_inc(v_f_x3f_493_);
lean_inc_ref(v_inst_492_);
lean_inc(v_toBind_491_);
v___f_534_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__11), 8, 7);
lean_closure_set(v___f_534_, 0, v_toPure_490_);
lean_closure_set(v___f_534_, 1, v_e_489_);
lean_closure_set(v___f_534_, 2, v_toBind_491_);
lean_closure_set(v___f_534_, 3, v_fn_532_);
lean_closure_set(v___f_534_, 4, v_arg_533_);
lean_closure_set(v___f_534_, 5, v_inst_492_);
lean_closure_set(v___f_534_, 6, v_f_x3f_493_);
v___x_535_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_492_, v_f_x3f_493_, v_fn_532_, v_snd_531_);
v___x_536_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_535_, v___f_534_);
return v___x_536_;
}
case 11:
{
lean_object* v_snd_537_; lean_object* v_struct_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec(v___f_496_);
lean_dec(v___f_494_);
lean_dec(v_toPure_490_);
v_snd_537_ = lean_ctor_get(v_____x_497_, 1);
lean_inc(v_snd_537_);
lean_dec_ref(v_____x_497_);
v_struct_538_ = lean_ctor_get(v_e_489_, 2);
lean_inc_ref(v_struct_538_);
lean_dec_ref(v_e_489_);
v___x_539_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_492_, v_f_x3f_493_, v_struct_538_, v_snd_537_);
v___x_540_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_539_, v___f_495_);
return v___x_540_;
}
default: 
{
lean_object* v_snd_541_; lean_object* v___x_542_; 
lean_dec(v___f_495_);
lean_dec(v___f_494_);
lean_dec(v_f_x3f_493_);
lean_dec_ref(v_inst_492_);
lean_dec(v_toBind_491_);
lean_dec(v_toPure_490_);
v_snd_541_ = lean_ctor_get(v_____x_497_, 1);
lean_inc(v_snd_541_);
lean_dec_ref(v_____x_497_);
v___x_542_ = lean_apply_2(v___f_496_, v_e_489_, v_snd_541_);
return v___x_542_;
}
}
}
else
{
lean_object* v_snd_543_; lean_object* v___x_545_; uint8_t v_isShared_546_; uint8_t v_isSharedCheck_558_; 
lean_inc_ref(v_fst_498_);
lean_dec(v___f_496_);
lean_dec(v___f_495_);
lean_dec(v___f_494_);
lean_dec(v_f_x3f_493_);
lean_dec_ref(v_inst_492_);
v_snd_543_ = lean_ctor_get(v_____x_497_, 1);
v_isSharedCheck_558_ = !lean_is_exclusive(v_____x_497_);
if (v_isSharedCheck_558_ == 0)
{
lean_object* v_unused_559_; 
v_unused_559_ = lean_ctor_get(v_____x_497_, 0);
lean_dec(v_unused_559_);
v___x_545_ = v_____x_497_;
v_isShared_546_ = v_isSharedCheck_558_;
goto v_resetjp_544_;
}
else
{
lean_inc(v_snd_543_);
lean_dec(v_____x_497_);
v___x_545_ = lean_box(0);
v_isShared_546_ = v_isSharedCheck_558_;
goto v_resetjp_544_;
}
v_resetjp_544_:
{
lean_object* v_val_547_; lean_object* v___f_548_; lean_object* v___x_549_; lean_object* v___f_550_; lean_object* v___f_551_; lean_object* v___x_552_; lean_object* v___x_554_; 
v_val_547_ = lean_ctor_get(v_fst_498_, 0);
lean_inc_n(v_val_547_, 2);
lean_dec_ref(v_fst_498_);
lean_inc(v_toPure_490_);
v___f_548_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__13), 3, 2);
lean_closure_set(v___f_548_, 0, v_val_547_);
lean_closure_set(v___f_548_, 1, v_toPure_490_);
v___x_549_ = lean_box(0);
v___f_550_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__0));
v___f_551_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_cacheT___redArg___closed__1));
v___x_552_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___f_550_, v___f_551_, v_snd_543_, v_e_489_, v_val_547_);
if (v_isShared_546_ == 0)
{
lean_ctor_set(v___x_545_, 1, v___x_552_);
lean_ctor_set(v___x_545_, 0, v___x_549_);
v___x_554_ = v___x_545_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_557_; 
v_reuseFailAlloc_557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_557_, 0, v___x_549_);
lean_ctor_set(v_reuseFailAlloc_557_, 1, v___x_552_);
v___x_554_ = v_reuseFailAlloc_557_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_apply_2(v_toPure_490_, lean_box(0), v___x_554_);
v___x_556_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_555_, v___f_548_);
return v___x_556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(lean_object* v_inst_560_, lean_object* v_f_x3f_561_, lean_object* v_e_562_, lean_object* v_a_563_){
_start:
{
lean_object* v_toApplicative_564_; lean_object* v_toBind_565_; lean_object* v_toPure_566_; lean_object* v___f_567_; lean_object* v___f_568_; lean_object* v___f_569_; lean_object* v___f_570_; lean_object* v___f_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_toApplicative_564_ = lean_ctor_get(v_inst_560_, 0);
v_toBind_565_ = lean_ctor_get(v_inst_560_, 1);
lean_inc_n(v_toBind_565_, 5);
v_toPure_566_ = lean_ctor_get(v_toApplicative_564_, 1);
lean_inc_n(v_toPure_566_, 6);
lean_inc_ref_n(v_e_562_, 3);
v___f_567_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1), 4, 3);
lean_closure_set(v___f_567_, 0, v_toPure_566_);
lean_closure_set(v___f_567_, 1, v_e_562_);
lean_closure_set(v___f_567_, 2, v_toBind_565_);
v___f_568_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3), 4, 3);
lean_closure_set(v___f_568_, 0, v_toPure_566_);
lean_closure_set(v___f_568_, 1, v_e_562_);
lean_closure_set(v___f_568_, 2, v_toBind_565_);
v___f_569_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__2), 3, 1);
lean_closure_set(v___f_569_, 0, v_toPure_566_);
lean_inc_ref(v___f_569_);
lean_inc(v_f_x3f_561_);
v___f_570_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__14), 9, 8);
lean_closure_set(v___f_570_, 0, v_e_562_);
lean_closure_set(v___f_570_, 1, v_toPure_566_);
lean_closure_set(v___f_570_, 2, v_toBind_565_);
lean_closure_set(v___f_570_, 3, v_inst_560_);
lean_closure_set(v___f_570_, 4, v_f_x3f_561_);
lean_closure_set(v___f_570_, 5, v___f_567_);
lean_closure_set(v___f_570_, 6, v___f_568_);
lean_closure_set(v___f_570_, 7, v___f_569_);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__16), 7, 6);
lean_closure_set(v___f_571_, 0, v_e_562_);
lean_closure_set(v___f_571_, 1, v___f_569_);
lean_closure_set(v___f_571_, 2, v_f_x3f_561_);
lean_closure_set(v___f_571_, 3, v_toPure_566_);
lean_closure_set(v___f_571_, 4, v_toBind_565_);
lean_closure_set(v___f_571_, 5, v___f_570_);
lean_inc_ref(v_a_563_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_a_563_);
lean_ctor_set(v___x_572_, 1, v_a_563_);
v___x_573_ = lean_apply_2(v_toPure_566_, lean_box(0), v___x_572_);
v___x_574_ = lean_apply_4(v_toBind_565_, lean_box(0), lean_box(0), v___x_573_, v___f_571_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__8(lean_object* v_toPure_575_, lean_object* v_e_576_, lean_object* v_toBind_577_, lean_object* v_declName_578_, lean_object* v_fst_579_, uint8_t v_nondep_580_, lean_object* v_body_581_, lean_object* v_type_582_, lean_object* v_value_583_, lean_object* v_inst_584_, lean_object* v_f_x3f_585_, lean_object* v_____x_586_){
_start:
{
lean_object* v_fst_587_; lean_object* v_snd_588_; lean_object* v___x_589_; lean_object* v___f_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_fst_587_ = lean_ctor_get(v_____x_586_, 0);
lean_inc(v_fst_587_);
v_snd_588_ = lean_ctor_get(v_____x_586_, 1);
lean_inc(v_snd_588_);
lean_dec_ref(v_____x_586_);
v___x_589_ = lean_box(v_nondep_580_);
lean_inc_ref(v_body_581_);
lean_inc(v_toBind_577_);
v___f_590_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__9___boxed), 11, 10);
lean_closure_set(v___f_590_, 0, v_toPure_575_);
lean_closure_set(v___f_590_, 1, v_e_576_);
lean_closure_set(v___f_590_, 2, v_toBind_577_);
lean_closure_set(v___f_590_, 3, v_declName_578_);
lean_closure_set(v___f_590_, 4, v_fst_579_);
lean_closure_set(v___f_590_, 5, v_fst_587_);
lean_closure_set(v___f_590_, 6, v___x_589_);
lean_closure_set(v___f_590_, 7, v_body_581_);
lean_closure_set(v___f_590_, 8, v_type_582_);
lean_closure_set(v___f_590_, 9, v_value_583_);
v___x_591_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_584_, v_f_x3f_585_, v_body_581_, v_snd_588_);
v___x_592_ = lean_apply_4(v_toBind_577_, lean_box(0), lean_box(0), v___x_591_, v___f_590_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__8___boxed(lean_object* v_toPure_593_, lean_object* v_e_594_, lean_object* v_toBind_595_, lean_object* v_declName_596_, lean_object* v_fst_597_, lean_object* v_nondep_598_, lean_object* v_body_599_, lean_object* v_type_600_, lean_object* v_value_601_, lean_object* v_inst_602_, lean_object* v_f_x3f_603_, lean_object* v_____x_604_){
_start:
{
uint8_t v_nondep_4222__boxed_605_; lean_object* v_res_606_; 
v_nondep_4222__boxed_605_ = lean_unbox(v_nondep_598_);
v_res_606_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__8(v_toPure_593_, v_e_594_, v_toBind_595_, v_declName_596_, v_fst_597_, v_nondep_4222__boxed_605_, v_body_599_, v_type_600_, v_value_601_, v_inst_602_, v_f_x3f_603_, v_____x_604_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__10(lean_object* v_toPure_607_, lean_object* v_e_608_, lean_object* v_toBind_609_, lean_object* v_declName_610_, uint8_t v_nondep_611_, lean_object* v_body_612_, lean_object* v_type_613_, lean_object* v_value_614_, lean_object* v_inst_615_, lean_object* v_f_x3f_616_, lean_object* v_____x_617_){
_start:
{
lean_object* v_fst_618_; lean_object* v_snd_619_; lean_object* v___x_620_; lean_object* v___f_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
v_fst_618_ = lean_ctor_get(v_____x_617_, 0);
lean_inc(v_fst_618_);
v_snd_619_ = lean_ctor_get(v_____x_617_, 1);
lean_inc(v_snd_619_);
lean_dec_ref(v_____x_617_);
v___x_620_ = lean_box(v_nondep_611_);
lean_inc(v_f_x3f_616_);
lean_inc_ref(v_inst_615_);
lean_inc_ref(v_value_614_);
lean_inc(v_toBind_609_);
v___f_621_ = lean_alloc_closure((void*)(l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__8___boxed), 12, 11);
lean_closure_set(v___f_621_, 0, v_toPure_607_);
lean_closure_set(v___f_621_, 1, v_e_608_);
lean_closure_set(v___f_621_, 2, v_toBind_609_);
lean_closure_set(v___f_621_, 3, v_declName_610_);
lean_closure_set(v___f_621_, 4, v_fst_618_);
lean_closure_set(v___f_621_, 5, v___x_620_);
lean_closure_set(v___f_621_, 6, v_body_612_);
lean_closure_set(v___f_621_, 7, v_type_613_);
lean_closure_set(v___f_621_, 8, v_value_614_);
lean_closure_set(v___f_621_, 9, v_inst_615_);
lean_closure_set(v___f_621_, 10, v_f_x3f_616_);
v___x_622_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_615_, v_f_x3f_616_, v_value_614_, v_snd_619_);
v___x_623_ = lean_apply_4(v_toBind_609_, lean_box(0), lean_box(0), v___x_622_, v___f_621_);
return v___x_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit(lean_object* v_m_624_, lean_object* v_inst_625_, lean_object* v_f_x3f_626_, lean_object* v_e_627_, lean_object* v_a_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_625_, v_f_x3f_626_, v_e_627_, v_a_628_);
return v___x_629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT___redArg(lean_object* v_inst_630_, lean_object* v_f_x3f_631_, lean_object* v_e_632_, lean_object* v_a_633_){
_start:
{
lean_object* v___x_634_; 
v___x_634_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_630_, v_f_x3f_631_, v_e_632_, v_a_633_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT(lean_object* v_m_635_, lean_object* v_inst_636_, lean_object* v_f_x3f_637_, lean_object* v_e_638_, lean_object* v_a_639_){
_start:
{
lean_object* v___x_640_; 
v___x_640_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_636_, v_f_x3f_637_, v_e_638_, v_a_639_);
return v___x_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___lam__0(lean_object* v_x_641_){
_start:
{
lean_object* v_fst_642_; 
v_fst_642_ = lean_ctor_get(v_x_641_, 0);
lean_inc(v_fst_642_);
return v_fst_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___lam__0___boxed(lean_object* v_x_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___lam__0(v_x_643_);
lean_dec_ref(v_x_643_);
return v_res_644_;
}
}
static lean_object* _init_l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(64u);
v___x_647_ = l_Lean_mkPtrMap___redArg(v___x_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg(lean_object* v_inst_648_, lean_object* v_f_x3f_649_, lean_object* v_e_650_){
_start:
{
lean_object* v_toApplicative_651_; lean_object* v_toFunctor_652_; lean_object* v_map_653_; lean_object* v___f_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v_toApplicative_651_ = lean_ctor_get(v_inst_648_, 0);
v_toFunctor_652_ = lean_ctor_get(v_toApplicative_651_, 0);
v_map_653_ = lean_ctor_get(v_toFunctor_652_, 0);
lean_inc(v_map_653_);
v___f_654_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__0));
v___x_655_ = lean_obj_once(&l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1, &l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1_once, _init_l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1);
v___x_656_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_648_, v_f_x3f_649_, v_e_650_, v___x_655_);
v___x_657_ = lean_apply_4(v_map_653_, lean_box(0), lean_box(0), v___f_654_, v___x_656_);
return v___x_657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27(lean_object* v_m_658_, lean_object* v_inst_659_, lean_object* v_f_x3f_660_, lean_object* v_e_661_){
_start:
{
lean_object* v_toApplicative_662_; lean_object* v_toFunctor_663_; lean_object* v_map_664_; lean_object* v___f_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v_toApplicative_662_ = lean_ctor_get(v_inst_659_, 0);
v_toFunctor_663_ = lean_ctor_get(v_toApplicative_662_, 0);
v_map_664_ = lean_ctor_get(v_toFunctor_663_, 0);
lean_inc(v_map_664_);
v___f_665_ = ((lean_object*)(l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__0));
v___x_666_ = lean_obj_once(&l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1, &l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1_once, _init_l_Lean_Expr_ReplaceImpl_replaceUnsafe_x27___redArg___closed__1);
v___x_667_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg(v_inst_659_, v_f_x3f_660_, v_e_661_, v___x_666_);
v___x_668_ = lean_apply_4(v_map_664_, lean_box(0), lean_box(0), v___f_665_, v___x_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__0(lean_object* v_e_669_, lean_object* v_toPure_670_, lean_object* v_____do__lift_671_){
_start:
{
if (lean_obj_tag(v_e_669_) == 10)
{
lean_object* v_data_672_; lean_object* v_expr_673_; size_t v___x_674_; size_t v___x_675_; uint8_t v___x_676_; 
v_data_672_ = lean_ctor_get(v_e_669_, 0);
v_expr_673_ = lean_ctor_get(v_e_669_, 1);
v___x_674_ = lean_ptr_addr(v_expr_673_);
v___x_675_ = lean_ptr_addr(v_____do__lift_671_);
v___x_676_ = lean_usize_dec_eq(v___x_674_, v___x_675_);
if (v___x_676_ == 0)
{
lean_object* v___x_677_; lean_object* v___x_678_; 
lean_inc(v_data_672_);
lean_dec_ref(v_e_669_);
v___x_677_ = l_Lean_Expr_mdata___override(v_data_672_, v_____do__lift_671_);
v___x_678_ = lean_apply_2(v_toPure_670_, lean_box(0), v___x_677_);
return v___x_678_;
}
else
{
lean_object* v___x_679_; 
lean_dec_ref(v_____do__lift_671_);
v___x_679_ = lean_apply_2(v_toPure_670_, lean_box(0), v_e_669_);
return v___x_679_;
}
}
else
{
lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec_ref(v_____do__lift_671_);
lean_dec_ref(v_e_669_);
v___x_680_ = l_Lean_instInhabitedExpr;
v___x_681_ = lean_obj_once(&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3, &l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3_once, _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__1___closed__3);
v___x_682_ = l_panic___redArg(v___x_680_, v___x_681_);
v___x_683_ = lean_apply_2(v_toPure_670_, lean_box(0), v___x_682_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__1(lean_object* v_e_684_, lean_object* v_toPure_685_, lean_object* v_____do__lift_686_){
_start:
{
if (lean_obj_tag(v_e_684_) == 11)
{
lean_object* v_typeName_687_; lean_object* v_idx_688_; lean_object* v_struct_689_; size_t v___x_690_; size_t v___x_691_; uint8_t v___x_692_; 
v_typeName_687_ = lean_ctor_get(v_e_684_, 0);
v_idx_688_ = lean_ctor_get(v_e_684_, 1);
v_struct_689_ = lean_ctor_get(v_e_684_, 2);
v___x_690_ = lean_ptr_addr(v_struct_689_);
v___x_691_ = lean_ptr_addr(v_____do__lift_686_);
v___x_692_ = lean_usize_dec_eq(v___x_690_, v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; lean_object* v___x_694_; 
lean_inc(v_idx_688_);
lean_inc(v_typeName_687_);
lean_dec_ref(v_e_684_);
v___x_693_ = l_Lean_Expr_proj___override(v_typeName_687_, v_idx_688_, v_____do__lift_686_);
v___x_694_ = lean_apply_2(v_toPure_685_, lean_box(0), v___x_693_);
return v___x_694_;
}
else
{
lean_object* v___x_695_; 
lean_dec_ref(v_____do__lift_686_);
v___x_695_ = lean_apply_2(v_toPure_685_, lean_box(0), v_e_684_);
return v___x_695_;
}
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; 
lean_dec_ref(v_____do__lift_686_);
lean_dec_ref(v_e_684_);
v___x_696_ = l_Lean_instInhabitedExpr;
v___x_697_ = lean_obj_once(&l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2, &l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2_once, _init_l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___redArg___lam__3___closed__2);
v___x_698_ = l_panic___redArg(v___x_696_, v___x_697_);
v___x_699_ = lean_apply_2(v_toPure_685_, lean_box(0), v___x_698_);
return v___x_699_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__2(lean_object* v_binderName_700_, lean_object* v_____do__lift_701_, uint8_t v_binderInfo_702_, lean_object* v_toPure_703_, lean_object* v_e_704_, lean_object* v_binderType_705_, lean_object* v_body_706_, lean_object* v_____do__lift_707_){
_start:
{
uint8_t v___y_709_; size_t v___x_716_; size_t v___x_717_; uint8_t v___x_718_; 
v___x_716_ = lean_ptr_addr(v_binderType_705_);
v___x_717_ = lean_ptr_addr(v_____do__lift_701_);
v___x_718_ = lean_usize_dec_eq(v___x_716_, v___x_717_);
if (v___x_718_ == 0)
{
v___y_709_ = v___x_718_;
goto v___jp_708_;
}
else
{
size_t v___x_719_; size_t v___x_720_; uint8_t v___x_721_; 
v___x_719_ = lean_ptr_addr(v_body_706_);
v___x_720_ = lean_ptr_addr(v_____do__lift_707_);
v___x_721_ = lean_usize_dec_eq(v___x_719_, v___x_720_);
v___y_709_ = v___x_721_;
goto v___jp_708_;
}
v___jp_708_:
{
if (v___y_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec_ref(v_e_704_);
v___x_710_ = l_Lean_Expr_forallE___override(v_binderName_700_, v_____do__lift_701_, v_____do__lift_707_, v_binderInfo_702_);
v___x_711_ = lean_apply_2(v_toPure_703_, lean_box(0), v___x_710_);
return v___x_711_;
}
else
{
uint8_t v___x_712_; 
v___x_712_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_702_, v_binderInfo_702_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec_ref(v_e_704_);
v___x_713_ = l_Lean_Expr_forallE___override(v_binderName_700_, v_____do__lift_701_, v_____do__lift_707_, v_binderInfo_702_);
v___x_714_ = lean_apply_2(v_toPure_703_, lean_box(0), v___x_713_);
return v___x_714_;
}
else
{
lean_object* v___x_715_; 
lean_dec_ref(v_____do__lift_707_);
lean_dec_ref(v_____do__lift_701_);
lean_dec(v_binderName_700_);
v___x_715_ = lean_apply_2(v_toPure_703_, lean_box(0), v_e_704_);
return v___x_715_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__2___boxed(lean_object* v_binderName_722_, lean_object* v_____do__lift_723_, lean_object* v_binderInfo_724_, lean_object* v_toPure_725_, lean_object* v_e_726_, lean_object* v_binderType_727_, lean_object* v_body_728_, lean_object* v_____do__lift_729_){
_start:
{
uint8_t v_binderInfo_886__boxed_730_; lean_object* v_res_731_; 
v_binderInfo_886__boxed_730_ = lean_unbox(v_binderInfo_724_);
v_res_731_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__2(v_binderName_722_, v_____do__lift_723_, v_binderInfo_886__boxed_730_, v_toPure_725_, v_e_726_, v_binderType_727_, v_body_728_, v_____do__lift_729_);
lean_dec_ref(v_body_728_);
lean_dec_ref(v_binderType_727_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__9(lean_object* v_____do__lift_732_, lean_object* v_toPure_733_, lean_object* v_e_734_, lean_object* v_fn_735_, lean_object* v_arg_736_, lean_object* v_____do__lift_737_){
_start:
{
uint8_t v___y_739_; size_t v___x_743_; size_t v___x_744_; uint8_t v___x_745_; 
v___x_743_ = lean_ptr_addr(v_fn_735_);
v___x_744_ = lean_ptr_addr(v_____do__lift_732_);
v___x_745_ = lean_usize_dec_eq(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
v___y_739_ = v___x_745_;
goto v___jp_738_;
}
else
{
size_t v___x_746_; size_t v___x_747_; uint8_t v___x_748_; 
v___x_746_ = lean_ptr_addr(v_arg_736_);
v___x_747_ = lean_ptr_addr(v_____do__lift_737_);
v___x_748_ = lean_usize_dec_eq(v___x_746_, v___x_747_);
v___y_739_ = v___x_748_;
goto v___jp_738_;
}
v___jp_738_:
{
if (v___y_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec_ref(v_e_734_);
v___x_740_ = l_Lean_Expr_app___override(v_____do__lift_732_, v_____do__lift_737_);
v___x_741_ = lean_apply_2(v_toPure_733_, lean_box(0), v___x_740_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; 
lean_dec_ref(v_____do__lift_737_);
lean_dec_ref(v_____do__lift_732_);
v___x_742_ = lean_apply_2(v_toPure_733_, lean_box(0), v_e_734_);
return v___x_742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__9___boxed(lean_object* v_____do__lift_749_, lean_object* v_toPure_750_, lean_object* v_e_751_, lean_object* v_fn_752_, lean_object* v_arg_753_, lean_object* v_____do__lift_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__9(v_____do__lift_749_, v_toPure_750_, v_e_751_, v_fn_752_, v_arg_753_, v_____do__lift_754_);
lean_dec_ref(v_arg_753_);
lean_dec_ref(v_fn_752_);
return v_res_755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__6(lean_object* v_declName_756_, lean_object* v_____do__lift_757_, lean_object* v_____do__lift_758_, uint8_t v_nondep_759_, lean_object* v_toPure_760_, lean_object* v_body_761_, lean_object* v_e_762_, lean_object* v_type_763_, lean_object* v_value_764_, lean_object* v_____do__lift_765_){
_start:
{
uint8_t v___y_767_; size_t v___x_776_; size_t v___x_777_; uint8_t v___x_778_; 
v___x_776_ = lean_ptr_addr(v_type_763_);
v___x_777_ = lean_ptr_addr(v_____do__lift_757_);
v___x_778_ = lean_usize_dec_eq(v___x_776_, v___x_777_);
if (v___x_778_ == 0)
{
v___y_767_ = v___x_778_;
goto v___jp_766_;
}
else
{
size_t v___x_779_; size_t v___x_780_; uint8_t v___x_781_; 
v___x_779_ = lean_ptr_addr(v_value_764_);
v___x_780_ = lean_ptr_addr(v_____do__lift_758_);
v___x_781_ = lean_usize_dec_eq(v___x_779_, v___x_780_);
v___y_767_ = v___x_781_;
goto v___jp_766_;
}
v___jp_766_:
{
if (v___y_767_ == 0)
{
lean_object* v___x_768_; lean_object* v___x_769_; 
lean_dec_ref(v_e_762_);
v___x_768_ = l_Lean_Expr_letE___override(v_declName_756_, v_____do__lift_757_, v_____do__lift_758_, v_____do__lift_765_, v_nondep_759_);
v___x_769_ = lean_apply_2(v_toPure_760_, lean_box(0), v___x_768_);
return v___x_769_;
}
else
{
size_t v___x_770_; size_t v___x_771_; uint8_t v___x_772_; 
v___x_770_ = lean_ptr_addr(v_body_761_);
v___x_771_ = lean_ptr_addr(v_____do__lift_765_);
v___x_772_ = lean_usize_dec_eq(v___x_770_, v___x_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; lean_object* v___x_774_; 
lean_dec_ref(v_e_762_);
v___x_773_ = l_Lean_Expr_letE___override(v_declName_756_, v_____do__lift_757_, v_____do__lift_758_, v_____do__lift_765_, v_nondep_759_);
v___x_774_ = lean_apply_2(v_toPure_760_, lean_box(0), v___x_773_);
return v___x_774_;
}
else
{
lean_object* v___x_775_; 
lean_dec_ref(v_____do__lift_765_);
lean_dec_ref(v_____do__lift_758_);
lean_dec_ref(v_____do__lift_757_);
lean_dec(v_declName_756_);
v___x_775_ = lean_apply_2(v_toPure_760_, lean_box(0), v_e_762_);
return v___x_775_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__6___boxed(lean_object* v_declName_782_, lean_object* v_____do__lift_783_, lean_object* v_____do__lift_784_, lean_object* v_nondep_785_, lean_object* v_toPure_786_, lean_object* v_body_787_, lean_object* v_e_788_, lean_object* v_type_789_, lean_object* v_value_790_, lean_object* v_____do__lift_791_){
_start:
{
uint8_t v_nondep_967__boxed_792_; lean_object* v_res_793_; 
v_nondep_967__boxed_792_ = lean_unbox(v_nondep_785_);
v_res_793_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__6(v_declName_782_, v_____do__lift_783_, v_____do__lift_784_, v_nondep_967__boxed_792_, v_toPure_786_, v_body_787_, v_e_788_, v_type_789_, v_value_790_, v_____do__lift_791_);
lean_dec_ref(v_value_790_);
lean_dec_ref(v_type_789_);
lean_dec_ref(v_body_787_);
return v_res_793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__4(lean_object* v_binderName_794_, lean_object* v_____do__lift_795_, uint8_t v_binderInfo_796_, lean_object* v_toPure_797_, lean_object* v_e_798_, lean_object* v_binderType_799_, lean_object* v_body_800_, lean_object* v_____do__lift_801_){
_start:
{
uint8_t v___y_803_; size_t v___x_810_; size_t v___x_811_; uint8_t v___x_812_; 
v___x_810_ = lean_ptr_addr(v_binderType_799_);
v___x_811_ = lean_ptr_addr(v_____do__lift_795_);
v___x_812_ = lean_usize_dec_eq(v___x_810_, v___x_811_);
if (v___x_812_ == 0)
{
v___y_803_ = v___x_812_;
goto v___jp_802_;
}
else
{
size_t v___x_813_; size_t v___x_814_; uint8_t v___x_815_; 
v___x_813_ = lean_ptr_addr(v_body_800_);
v___x_814_ = lean_ptr_addr(v_____do__lift_801_);
v___x_815_ = lean_usize_dec_eq(v___x_813_, v___x_814_);
v___y_803_ = v___x_815_;
goto v___jp_802_;
}
v___jp_802_:
{
if (v___y_803_ == 0)
{
lean_object* v___x_804_; lean_object* v___x_805_; 
lean_dec_ref(v_e_798_);
v___x_804_ = l_Lean_Expr_lam___override(v_binderName_794_, v_____do__lift_795_, v_____do__lift_801_, v_binderInfo_796_);
v___x_805_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_804_);
return v___x_805_;
}
else
{
uint8_t v___x_806_; 
v___x_806_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_796_, v_binderInfo_796_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_e_798_);
v___x_807_ = l_Lean_Expr_lam___override(v_binderName_794_, v_____do__lift_795_, v_____do__lift_801_, v_binderInfo_796_);
v___x_808_ = lean_apply_2(v_toPure_797_, lean_box(0), v___x_807_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; 
lean_dec_ref(v_____do__lift_801_);
lean_dec_ref(v_____do__lift_795_);
lean_dec(v_binderName_794_);
v___x_809_ = lean_apply_2(v_toPure_797_, lean_box(0), v_e_798_);
return v___x_809_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__4___boxed(lean_object* v_binderName_816_, lean_object* v_____do__lift_817_, lean_object* v_binderInfo_818_, lean_object* v_toPure_819_, lean_object* v_e_820_, lean_object* v_binderType_821_, lean_object* v_body_822_, lean_object* v_____do__lift_823_){
_start:
{
uint8_t v_binderInfo_1022__boxed_824_; lean_object* v_res_825_; 
v_binderInfo_1022__boxed_824_ = lean_unbox(v_binderInfo_818_);
v_res_825_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__4(v_binderName_816_, v_____do__lift_817_, v_binderInfo_1022__boxed_824_, v_toPure_819_, v_e_820_, v_binderType_821_, v_body_822_, v_____do__lift_823_);
lean_dec_ref(v_body_822_);
lean_dec_ref(v_binderType_821_);
return v_res_825_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__3(lean_object* v_binderName_826_, uint8_t v_binderInfo_827_, lean_object* v_toPure_828_, lean_object* v_e_829_, lean_object* v_binderType_830_, lean_object* v_body_831_, lean_object* v_inst_832_, lean_object* v_f_x3f_833_, lean_object* v_toBind_834_, lean_object* v_____do__lift_835_){
_start:
{
lean_object* v___x_836_; lean_object* v___f_837_; lean_object* v___x_838_; lean_object* v___x_839_; 
v___x_836_ = lean_box(v_binderInfo_827_);
lean_inc_ref(v_body_831_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_837_, 0, v_binderName_826_);
lean_closure_set(v___f_837_, 1, v_____do__lift_835_);
lean_closure_set(v___f_837_, 2, v___x_836_);
lean_closure_set(v___f_837_, 3, v_toPure_828_);
lean_closure_set(v___f_837_, 4, v_e_829_);
lean_closure_set(v___f_837_, 5, v_binderType_830_);
lean_closure_set(v___f_837_, 6, v_body_831_);
v___x_838_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_832_, v_f_x3f_833_, v_body_831_);
v___x_839_ = lean_apply_4(v_toBind_834_, lean_box(0), lean_box(0), v___x_838_, v___f_837_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__3___boxed(lean_object* v_binderName_840_, lean_object* v_binderInfo_841_, lean_object* v_toPure_842_, lean_object* v_e_843_, lean_object* v_binderType_844_, lean_object* v_body_845_, lean_object* v_inst_846_, lean_object* v_f_x3f_847_, lean_object* v_toBind_848_, lean_object* v_____do__lift_849_){
_start:
{
uint8_t v_binderInfo_1074__boxed_850_; lean_object* v_res_851_; 
v_binderInfo_1074__boxed_850_ = lean_unbox(v_binderInfo_841_);
v_res_851_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__3(v_binderName_840_, v_binderInfo_1074__boxed_850_, v_toPure_842_, v_e_843_, v_binderType_844_, v_body_845_, v_inst_846_, v_f_x3f_847_, v_toBind_848_, v_____do__lift_849_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__5(lean_object* v_binderName_852_, uint8_t v_binderInfo_853_, lean_object* v_toPure_854_, lean_object* v_e_855_, lean_object* v_binderType_856_, lean_object* v_body_857_, lean_object* v_inst_858_, lean_object* v_f_x3f_859_, lean_object* v_toBind_860_, lean_object* v_____do__lift_861_){
_start:
{
lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_862_ = lean_box(v_binderInfo_853_);
lean_inc_ref(v_body_857_);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__4___boxed), 8, 7);
lean_closure_set(v___f_863_, 0, v_binderName_852_);
lean_closure_set(v___f_863_, 1, v_____do__lift_861_);
lean_closure_set(v___f_863_, 2, v___x_862_);
lean_closure_set(v___f_863_, 3, v_toPure_854_);
lean_closure_set(v___f_863_, 4, v_e_855_);
lean_closure_set(v___f_863_, 5, v_binderType_856_);
lean_closure_set(v___f_863_, 6, v_body_857_);
v___x_864_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_858_, v_f_x3f_859_, v_body_857_);
v___x_865_ = lean_apply_4(v_toBind_860_, lean_box(0), lean_box(0), v___x_864_, v___f_863_);
return v___x_865_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__5___boxed(lean_object* v_binderName_866_, lean_object* v_binderInfo_867_, lean_object* v_toPure_868_, lean_object* v_e_869_, lean_object* v_binderType_870_, lean_object* v_body_871_, lean_object* v_inst_872_, lean_object* v_f_x3f_873_, lean_object* v_toBind_874_, lean_object* v_____do__lift_875_){
_start:
{
uint8_t v_binderInfo_1083__boxed_876_; lean_object* v_res_877_; 
v_binderInfo_1083__boxed_876_ = lean_unbox(v_binderInfo_867_);
v_res_877_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__5(v_binderName_866_, v_binderInfo_1083__boxed_876_, v_toPure_868_, v_e_869_, v_binderType_870_, v_body_871_, v_inst_872_, v_f_x3f_873_, v_toBind_874_, v_____do__lift_875_);
return v_res_877_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__7(lean_object* v_declName_878_, lean_object* v_____do__lift_879_, uint8_t v_nondep_880_, lean_object* v_toPure_881_, lean_object* v_body_882_, lean_object* v_e_883_, lean_object* v_type_884_, lean_object* v_value_885_, lean_object* v_inst_886_, lean_object* v_f_x3f_887_, lean_object* v_toBind_888_, lean_object* v_____do__lift_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___f_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_890_ = lean_box(v_nondep_880_);
lean_inc_ref(v_body_882_);
v___f_891_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__6___boxed), 10, 9);
lean_closure_set(v___f_891_, 0, v_declName_878_);
lean_closure_set(v___f_891_, 1, v_____do__lift_879_);
lean_closure_set(v___f_891_, 2, v_____do__lift_889_);
lean_closure_set(v___f_891_, 3, v___x_890_);
lean_closure_set(v___f_891_, 4, v_toPure_881_);
lean_closure_set(v___f_891_, 5, v_body_882_);
lean_closure_set(v___f_891_, 6, v_e_883_);
lean_closure_set(v___f_891_, 7, v_type_884_);
lean_closure_set(v___f_891_, 8, v_value_885_);
v___x_892_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_886_, v_f_x3f_887_, v_body_882_);
v___x_893_ = lean_apply_4(v_toBind_888_, lean_box(0), lean_box(0), v___x_892_, v___f_891_);
return v___x_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__7___boxed(lean_object* v_declName_894_, lean_object* v_____do__lift_895_, lean_object* v_nondep_896_, lean_object* v_toPure_897_, lean_object* v_body_898_, lean_object* v_e_899_, lean_object* v_type_900_, lean_object* v_value_901_, lean_object* v_inst_902_, lean_object* v_f_x3f_903_, lean_object* v_toBind_904_, lean_object* v_____do__lift_905_){
_start:
{
uint8_t v_nondep_1093__boxed_906_; lean_object* v_res_907_; 
v_nondep_1093__boxed_906_ = lean_unbox(v_nondep_896_);
v_res_907_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__7(v_declName_894_, v_____do__lift_895_, v_nondep_1093__boxed_906_, v_toPure_897_, v_body_898_, v_e_899_, v_type_900_, v_value_901_, v_inst_902_, v_f_x3f_903_, v_toBind_904_, v_____do__lift_905_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__8(lean_object* v_declName_908_, uint8_t v_nondep_909_, lean_object* v_toPure_910_, lean_object* v_body_911_, lean_object* v_e_912_, lean_object* v_type_913_, lean_object* v_value_914_, lean_object* v_inst_915_, lean_object* v_f_x3f_916_, lean_object* v_toBind_917_, lean_object* v_____do__lift_918_){
_start:
{
lean_object* v___x_919_; lean_object* v___f_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_919_ = lean_box(v_nondep_909_);
lean_inc(v_toBind_917_);
lean_inc(v_f_x3f_916_);
lean_inc_ref(v_inst_915_);
lean_inc_ref(v_value_914_);
v___f_920_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__7___boxed), 12, 11);
lean_closure_set(v___f_920_, 0, v_declName_908_);
lean_closure_set(v___f_920_, 1, v_____do__lift_918_);
lean_closure_set(v___f_920_, 2, v___x_919_);
lean_closure_set(v___f_920_, 3, v_toPure_910_);
lean_closure_set(v___f_920_, 4, v_body_911_);
lean_closure_set(v___f_920_, 5, v_e_912_);
lean_closure_set(v___f_920_, 6, v_type_913_);
lean_closure_set(v___f_920_, 7, v_value_914_);
lean_closure_set(v___f_920_, 8, v_inst_915_);
lean_closure_set(v___f_920_, 9, v_f_x3f_916_);
lean_closure_set(v___f_920_, 10, v_toBind_917_);
v___x_921_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_915_, v_f_x3f_916_, v_value_914_);
v___x_922_ = lean_apply_4(v_toBind_917_, lean_box(0), lean_box(0), v___x_921_, v___f_920_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__8___boxed(lean_object* v_declName_923_, lean_object* v_nondep_924_, lean_object* v_toPure_925_, lean_object* v_body_926_, lean_object* v_e_927_, lean_object* v_type_928_, lean_object* v_value_929_, lean_object* v_inst_930_, lean_object* v_f_x3f_931_, lean_object* v_toBind_932_, lean_object* v_____do__lift_933_){
_start:
{
uint8_t v_nondep_1103__boxed_934_; lean_object* v_res_935_; 
v_nondep_1103__boxed_934_ = lean_unbox(v_nondep_924_);
v_res_935_ = l_Lean_Expr_replaceNoCacheT___redArg___lam__8(v_declName_923_, v_nondep_1103__boxed_934_, v_toPure_925_, v_body_926_, v_e_927_, v_type_928_, v_value_929_, v_inst_930_, v_f_x3f_931_, v_toBind_932_, v_____do__lift_933_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__11(lean_object* v_e_936_, lean_object* v_toPure_937_, lean_object* v_inst_938_, lean_object* v_f_x3f_939_, lean_object* v_toBind_940_, lean_object* v___f_941_, lean_object* v___f_942_, lean_object* v_____do__lift_943_){
_start:
{
if (lean_obj_tag(v_____do__lift_943_) == 0)
{
switch(lean_obj_tag(v_e_936_))
{
case 7:
{
lean_object* v_binderName_944_; lean_object* v_binderType_945_; lean_object* v_body_946_; uint8_t v_binderInfo_947_; lean_object* v___x_948_; lean_object* v___f_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
lean_dec(v___f_942_);
lean_dec(v___f_941_);
v_binderName_944_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_binderName_944_);
v_binderType_945_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref_n(v_binderType_945_, 2);
v_body_946_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_body_946_);
v_binderInfo_947_ = lean_ctor_get_uint8(v_e_936_, sizeof(void*)*3 + 8);
v___x_948_ = lean_box(v_binderInfo_947_);
lean_inc(v_toBind_940_);
lean_inc(v_f_x3f_939_);
lean_inc_ref(v_inst_938_);
v___f_949_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__3___boxed), 10, 9);
lean_closure_set(v___f_949_, 0, v_binderName_944_);
lean_closure_set(v___f_949_, 1, v___x_948_);
lean_closure_set(v___f_949_, 2, v_toPure_937_);
lean_closure_set(v___f_949_, 3, v_e_936_);
lean_closure_set(v___f_949_, 4, v_binderType_945_);
lean_closure_set(v___f_949_, 5, v_body_946_);
lean_closure_set(v___f_949_, 6, v_inst_938_);
lean_closure_set(v___f_949_, 7, v_f_x3f_939_);
lean_closure_set(v___f_949_, 8, v_toBind_940_);
v___x_950_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_938_, v_f_x3f_939_, v_binderType_945_);
v___x_951_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v___x_950_, v___f_949_);
return v___x_951_;
}
case 6:
{
lean_object* v_binderName_952_; lean_object* v_binderType_953_; lean_object* v_body_954_; uint8_t v_binderInfo_955_; lean_object* v___x_956_; lean_object* v___f_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
lean_dec(v___f_942_);
lean_dec(v___f_941_);
v_binderName_952_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_binderName_952_);
v_binderType_953_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref_n(v_binderType_953_, 2);
v_body_954_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_body_954_);
v_binderInfo_955_ = lean_ctor_get_uint8(v_e_936_, sizeof(void*)*3 + 8);
v___x_956_ = lean_box(v_binderInfo_955_);
lean_inc(v_toBind_940_);
lean_inc(v_f_x3f_939_);
lean_inc_ref(v_inst_938_);
v___f_957_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__5___boxed), 10, 9);
lean_closure_set(v___f_957_, 0, v_binderName_952_);
lean_closure_set(v___f_957_, 1, v___x_956_);
lean_closure_set(v___f_957_, 2, v_toPure_937_);
lean_closure_set(v___f_957_, 3, v_e_936_);
lean_closure_set(v___f_957_, 4, v_binderType_953_);
lean_closure_set(v___f_957_, 5, v_body_954_);
lean_closure_set(v___f_957_, 6, v_inst_938_);
lean_closure_set(v___f_957_, 7, v_f_x3f_939_);
lean_closure_set(v___f_957_, 8, v_toBind_940_);
v___x_958_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_938_, v_f_x3f_939_, v_binderType_953_);
v___x_959_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v___x_958_, v___f_957_);
return v___x_959_;
}
case 10:
{
lean_object* v_expr_960_; lean_object* v___x_961_; lean_object* v___x_962_; 
lean_dec(v___f_942_);
lean_dec(v_toPure_937_);
v_expr_960_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref(v_expr_960_);
lean_dec_ref(v_e_936_);
v___x_961_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_938_, v_f_x3f_939_, v_expr_960_);
v___x_962_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v___x_961_, v___f_941_);
return v___x_962_;
}
case 8:
{
lean_object* v_declName_963_; lean_object* v_type_964_; lean_object* v_value_965_; lean_object* v_body_966_; uint8_t v_nondep_967_; lean_object* v___x_968_; lean_object* v___f_969_; lean_object* v___x_970_; lean_object* v___x_971_; 
lean_dec(v___f_942_);
lean_dec(v___f_941_);
v_declName_963_ = lean_ctor_get(v_e_936_, 0);
lean_inc(v_declName_963_);
v_type_964_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref_n(v_type_964_, 2);
v_value_965_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_value_965_);
v_body_966_ = lean_ctor_get(v_e_936_, 3);
lean_inc_ref(v_body_966_);
v_nondep_967_ = lean_ctor_get_uint8(v_e_936_, sizeof(void*)*4 + 8);
v___x_968_ = lean_box(v_nondep_967_);
lean_inc(v_toBind_940_);
lean_inc(v_f_x3f_939_);
lean_inc_ref(v_inst_938_);
v___f_969_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__8___boxed), 11, 10);
lean_closure_set(v___f_969_, 0, v_declName_963_);
lean_closure_set(v___f_969_, 1, v___x_968_);
lean_closure_set(v___f_969_, 2, v_toPure_937_);
lean_closure_set(v___f_969_, 3, v_body_966_);
lean_closure_set(v___f_969_, 4, v_e_936_);
lean_closure_set(v___f_969_, 5, v_type_964_);
lean_closure_set(v___f_969_, 6, v_value_965_);
lean_closure_set(v___f_969_, 7, v_inst_938_);
lean_closure_set(v___f_969_, 8, v_f_x3f_939_);
lean_closure_set(v___f_969_, 9, v_toBind_940_);
v___x_970_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_938_, v_f_x3f_939_, v_type_964_);
v___x_971_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v___x_970_, v___f_969_);
return v___x_971_;
}
case 5:
{
lean_object* v_fn_972_; lean_object* v_arg_973_; lean_object* v___f_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v___f_942_);
lean_dec(v___f_941_);
v_fn_972_ = lean_ctor_get(v_e_936_, 0);
lean_inc_ref_n(v_fn_972_, 2);
v_arg_973_ = lean_ctor_get(v_e_936_, 1);
lean_inc_ref(v_arg_973_);
lean_inc(v_toBind_940_);
lean_inc(v_f_x3f_939_);
lean_inc_ref(v_inst_938_);
v___f_974_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__10), 8, 7);
lean_closure_set(v___f_974_, 0, v_toPure_937_);
lean_closure_set(v___f_974_, 1, v_e_936_);
lean_closure_set(v___f_974_, 2, v_fn_972_);
lean_closure_set(v___f_974_, 3, v_arg_973_);
lean_closure_set(v___f_974_, 4, v_inst_938_);
lean_closure_set(v___f_974_, 5, v_f_x3f_939_);
lean_closure_set(v___f_974_, 6, v_toBind_940_);
v___x_975_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_938_, v_f_x3f_939_, v_fn_972_);
v___x_976_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v___x_975_, v___f_974_);
return v___x_976_;
}
case 11:
{
lean_object* v_struct_977_; lean_object* v___x_978_; lean_object* v___x_979_; 
lean_dec(v___f_941_);
lean_dec(v_toPure_937_);
v_struct_977_ = lean_ctor_get(v_e_936_, 2);
lean_inc_ref(v_struct_977_);
lean_dec_ref(v_e_936_);
v___x_978_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_938_, v_f_x3f_939_, v_struct_977_);
v___x_979_ = lean_apply_4(v_toBind_940_, lean_box(0), lean_box(0), v___x_978_, v___f_942_);
return v___x_979_;
}
default: 
{
lean_object* v___x_980_; 
lean_dec(v___f_942_);
lean_dec(v___f_941_);
lean_dec(v_toBind_940_);
lean_dec(v_f_x3f_939_);
lean_dec_ref(v_inst_938_);
v___x_980_ = lean_apply_2(v_toPure_937_, lean_box(0), v_e_936_);
return v___x_980_;
}
}
}
else
{
lean_object* v_val_981_; lean_object* v___x_982_; 
lean_dec(v___f_942_);
lean_dec(v___f_941_);
lean_dec(v_toBind_940_);
lean_dec(v_f_x3f_939_);
lean_dec_ref(v_inst_938_);
lean_dec_ref(v_e_936_);
v_val_981_ = lean_ctor_get(v_____do__lift_943_, 0);
lean_inc(v_val_981_);
lean_dec_ref(v_____do__lift_943_);
v___x_982_ = lean_apply_2(v_toPure_937_, lean_box(0), v_val_981_);
return v___x_982_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg(lean_object* v_inst_983_, lean_object* v_f_x3f_984_, lean_object* v_e_985_){
_start:
{
lean_object* v_toApplicative_986_; lean_object* v_toBind_987_; lean_object* v_toPure_988_; lean_object* v___x_989_; lean_object* v___f_990_; lean_object* v___f_991_; lean_object* v___f_992_; lean_object* v___x_993_; 
v_toApplicative_986_ = lean_ctor_get(v_inst_983_, 0);
v_toBind_987_ = lean_ctor_get(v_inst_983_, 1);
lean_inc_n(v_toBind_987_, 2);
v_toPure_988_ = lean_ctor_get(v_toApplicative_986_, 1);
lean_inc_n(v_toPure_988_, 3);
lean_inc(v_f_x3f_984_);
lean_inc_ref_n(v_e_985_, 3);
v___x_989_ = lean_apply_1(v_f_x3f_984_, v_e_985_);
v___f_990_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_990_, 0, v_e_985_);
lean_closure_set(v___f_990_, 1, v_toPure_988_);
v___f_991_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__1), 3, 2);
lean_closure_set(v___f_991_, 0, v_e_985_);
lean_closure_set(v___f_991_, 1, v_toPure_988_);
v___f_992_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__11), 8, 7);
lean_closure_set(v___f_992_, 0, v_e_985_);
lean_closure_set(v___f_992_, 1, v_toPure_988_);
lean_closure_set(v___f_992_, 2, v_inst_983_);
lean_closure_set(v___f_992_, 3, v_f_x3f_984_);
lean_closure_set(v___f_992_, 4, v_toBind_987_);
lean_closure_set(v___f_992_, 5, v___f_990_);
lean_closure_set(v___f_992_, 6, v___f_991_);
v___x_993_ = lean_apply_4(v_toBind_987_, lean_box(0), lean_box(0), v___x_989_, v___f_992_);
return v___x_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT___redArg___lam__10(lean_object* v_toPure_994_, lean_object* v_e_995_, lean_object* v_fn_996_, lean_object* v_arg_997_, lean_object* v_inst_998_, lean_object* v_f_x3f_999_, lean_object* v_toBind_1000_, lean_object* v_____do__lift_1001_){
_start:
{
lean_object* v___f_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; 
lean_inc_ref(v_arg_997_);
v___f_1002_ = lean_alloc_closure((void*)(l_Lean_Expr_replaceNoCacheT___redArg___lam__9___boxed), 6, 5);
lean_closure_set(v___f_1002_, 0, v_____do__lift_1001_);
lean_closure_set(v___f_1002_, 1, v_toPure_994_);
lean_closure_set(v___f_1002_, 2, v_e_995_);
lean_closure_set(v___f_1002_, 3, v_fn_996_);
lean_closure_set(v___f_1002_, 4, v_arg_997_);
v___x_1003_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_998_, v_f_x3f_999_, v_arg_997_);
v___x_1004_ = lean_apply_4(v_toBind_1000_, lean_box(0), lean_box(0), v___x_1003_, v___f_1002_);
return v___x_1004_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_replaceNoCacheT(lean_object* v_m_1005_, lean_object* v_inst_1006_, lean_object* v_f_x3f_1007_, lean_object* v_e_1008_){
_start:
{
lean_object* v___x_1009_; 
v___x_1009_ = l_Lean_Expr_replaceNoCacheT___redArg(v_inst_1006_, v_f_x3f_1007_, v_e_1008_);
return v___x_1009_;
}
}
static lean_object* _init_l_Lean_Expr_natZero___closed__3(void){
_start:
{
lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1015_ = lean_box(0);
v___x_1016_ = ((lean_object*)(l_Lean_Expr_natZero___closed__2));
v___x_1017_ = l_Lean_Expr_const___override(v___x_1016_, v___x_1015_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Expr_natZero(void){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_obj_once(&l_Lean_Expr_natZero___closed__3, &l_Lean_Expr_natZero___closed__3_once, _init_l_Lean_Expr_natZero___closed__3);
return v___x_1018_;
}
}
static lean_object* _init_l_Lean_Expr_natSucc___closed__2(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1023_ = lean_box(0);
v___x_1024_ = ((lean_object*)(l_Lean_Expr_natSucc___closed__1));
v___x_1025_ = l_Lean_Expr_const___override(v___x_1024_, v___x_1023_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Expr_natSucc(void){
_start:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_obj_once(&l_Lean_Expr_natSucc___closed__2, &l_Lean_Expr_natSucc___closed__2_once, _init_l_Lean_Expr_natSucc___closed__2);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstructorApp_x3f_x27(lean_object* v_env_1027_, lean_object* v_e_1028_){
_start:
{
lean_object* v___x_1029_; 
v___x_1029_ = l_Lean_Expr_getAppFn(v_e_1028_);
if (lean_obj_tag(v___x_1029_) == 4)
{
lean_object* v_declName_1030_; lean_object* v___x_1031_; 
v_declName_1030_ = lean_ctor_get(v___x_1029_, 0);
lean_inc_n(v_declName_1030_, 2);
lean_dec_ref(v___x_1029_);
v___x_1031_ = lean_environment_find(v_env_1027_, v_declName_1030_);
if (lean_obj_tag(v___x_1031_) == 0)
{
lean_object* v___x_1032_; 
lean_dec(v_declName_1030_);
v___x_1032_ = lean_box(0);
return v___x_1032_;
}
else
{
lean_object* v_val_1033_; lean_object* v___x_1035_; uint8_t v_isShared_1036_; uint8_t v_isSharedCheck_1041_; 
v_val_1033_ = lean_ctor_get(v___x_1031_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1031_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1035_ = v___x_1031_;
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
else
{
lean_inc(v_val_1033_);
lean_dec(v___x_1031_);
v___x_1035_ = lean_box(0);
v_isShared_1036_ = v_isSharedCheck_1041_;
goto v_resetjp_1034_;
}
v_resetjp_1034_:
{
if (lean_obj_tag(v_val_1033_) == 6)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_val_1033_);
if (v_isShared_1036_ == 0)
{
lean_ctor_set(v___x_1035_, 0, v_declName_1030_);
v___x_1038_ = v___x_1035_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_declName_1030_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
else
{
lean_object* v___x_1040_; 
lean_del_object(v___x_1035_);
lean_dec(v_val_1033_);
lean_dec(v_declName_1030_);
v___x_1040_ = lean_box(0);
return v___x_1040_;
}
}
}
}
else
{
lean_object* v___x_1042_; 
lean_dec_ref(v___x_1029_);
lean_dec_ref(v_env_1027_);
v___x_1042_ = lean_box(0);
return v___x_1042_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_isConstructorApp_x3f_x27___boxed(lean_object* v_env_1043_, lean_object* v_e_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Expr_isConstructorApp_x3f_x27(v_env_1043_, v_e_1044_);
lean_dec_ref(v_e_1044_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_natLitToConstructor(lean_object* v_x_1046_){
_start:
{
lean_object* v_zero_1047_; uint8_t v_isZero_1048_; 
v_zero_1047_ = lean_unsigned_to_nat(0u);
v_isZero_1048_ = lean_nat_dec_eq(v_x_1046_, v_zero_1047_);
if (v_isZero_1048_ == 1)
{
lean_object* v___x_1049_; 
v___x_1049_ = l_Lean_Expr_natZero;
return v___x_1049_;
}
else
{
lean_object* v_one_1050_; lean_object* v_n_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; 
v_one_1050_ = lean_unsigned_to_nat(1u);
v_n_1051_ = lean_nat_sub(v_x_1046_, v_one_1050_);
v___x_1052_ = l_Lean_Expr_natSucc;
v___x_1053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1053_, 0, v_n_1051_);
v___x_1054_ = l_Lean_Expr_lit___override(v___x_1053_);
v___x_1055_ = l_Lean_Expr_app___override(v___x_1052_, v___x_1054_);
return v___x_1055_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_natLitToConstructor___boxed(lean_object* v_x_1056_){
_start:
{
lean_object* v_res_1057_; 
v_res_1057_ = l_Lean_Expr_natLitToConstructor(v_x_1056_);
lean_dec(v_x_1056_);
return v_res_1057_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v_charOfNat_1065_; 
v___x_1063_ = lean_box(0);
v___x_1064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__2));
v_charOfNat_1065_ = l_Lean_Expr_const___override(v___x_1064_, v___x_1063_);
return v_charOfNat_1065_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__8(void){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__4));
v___x_1075_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__7));
v___x_1076_ = l_Lean_Expr_const___override(v___x_1075_, v___x_1074_);
return v___x_1076_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v_char_1081_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__9));
v_char_1081_ = l_Lean_Expr_const___override(v___x_1080_, v___x_1079_);
return v_char_1081_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__11(void){
_start:
{
lean_object* v_char_1082_; lean_object* v___x_1083_; lean_object* v_listCons_1084_; 
v_char_1082_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10);
v___x_1083_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__8, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__8_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__8);
v_listCons_1084_ = l_Lean_Expr_app___override(v___x_1083_, v_char_1082_);
return v_listCons_1084_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0(lean_object* v_as_1085_, size_t v_i_1086_, size_t v_stop_1087_, lean_object* v_b_1088_){
_start:
{
lean_object* v_charOfNat_1089_; uint8_t v___x_1090_; 
v_charOfNat_1089_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__3, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__3);
v___x_1090_ = lean_usize_dec_eq(v_i_1086_, v_stop_1087_);
if (v___x_1090_ == 0)
{
lean_object* v_listCons_1091_; size_t v___x_1092_; size_t v___x_1093_; lean_object* v___x_1094_; uint32_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; 
v_listCons_1091_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__11, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__11_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__11);
v___x_1092_ = ((size_t)1ULL);
v___x_1093_ = lean_usize_sub(v_i_1086_, v___x_1092_);
v___x_1094_ = lean_array_uget_borrowed(v_as_1085_, v___x_1093_);
v___x_1095_ = lean_unbox_uint32(v___x_1094_);
v___x_1096_ = lean_uint32_to_nat(v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
v___x_1098_ = l_Lean_Expr_lit___override(v___x_1097_);
v___x_1099_ = l_Lean_Expr_app___override(v_charOfNat_1089_, v___x_1098_);
v___x_1100_ = l_Lean_Expr_app___override(v_listCons_1091_, v___x_1099_);
v___x_1101_ = l_Lean_Expr_app___override(v___x_1100_, v_b_1088_);
v_i_1086_ = v___x_1093_;
v_b_1088_ = v___x_1101_;
goto _start;
}
else
{
return v_b_1088_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___boxed(lean_object* v_as_1103_, lean_object* v_i_1104_, lean_object* v_stop_1105_, lean_object* v_b_1106_){
_start:
{
size_t v_i_boxed_1107_; size_t v_stop_boxed_1108_; lean_object* v_res_1109_; 
v_i_boxed_1107_ = lean_unbox_usize(v_i_1104_);
lean_dec(v_i_1104_);
v_stop_boxed_1108_ = lean_unbox_usize(v_stop_1105_);
lean_dec(v_stop_1105_);
v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0(v_as_1103_, v_i_boxed_1107_, v_stop_boxed_1108_, v_b_1106_);
lean_dec_ref(v_as_1103_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0(lean_object* v_init_1110_, lean_object* v_l_1111_){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; uint8_t v___x_1115_; 
v___x_1112_ = lean_array_mk(v_l_1111_);
v___x_1113_ = lean_array_get_size(v___x_1112_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_nat_dec_lt(v___x_1114_, v___x_1113_);
if (v___x_1115_ == 0)
{
lean_dec_ref(v___x_1112_);
return v_init_1110_;
}
else
{
size_t v___x_1116_; size_t v___x_1117_; lean_object* v___x_1118_; 
v___x_1116_ = lean_usize_of_nat(v___x_1113_);
v___x_1117_ = ((size_t)0ULL);
v___x_1118_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0(v___x_1112_, v___x_1116_, v___x_1117_, v_init_1110_);
lean_dec_ref(v___x_1112_);
return v___x_1118_;
}
}
}
static lean_object* _init_l_Lean_Expr_strLitToConstructor___closed__2(void){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v___x_1123_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__4));
v___x_1124_ = ((lean_object*)(l_Lean_Expr_strLitToConstructor___closed__1));
v___x_1125_ = l_Lean_Expr_const___override(v___x_1124_, v___x_1123_);
return v___x_1125_;
}
}
static lean_object* _init_l_Lean_Expr_strLitToConstructor___closed__3(void){
_start:
{
lean_object* v_char_1126_; lean_object* v___x_1127_; lean_object* v_listNil_1128_; 
v_char_1126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10, &l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10_once, _init_l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0_spec__0___closed__10);
v___x_1127_ = lean_obj_once(&l_Lean_Expr_strLitToConstructor___closed__2, &l_Lean_Expr_strLitToConstructor___closed__2_once, _init_l_Lean_Expr_strLitToConstructor___closed__2);
v_listNil_1128_ = l_Lean_Expr_app___override(v___x_1127_, v_char_1126_);
return v_listNil_1128_;
}
}
static lean_object* _init_l_Lean_Expr_strLitToConstructor___closed__7(void){
_start:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v_stringMk_1136_; 
v___x_1134_ = lean_box(0);
v___x_1135_ = ((lean_object*)(l_Lean_Expr_strLitToConstructor___closed__6));
v_stringMk_1136_ = l_Lean_Expr_const___override(v___x_1135_, v___x_1134_);
return v_stringMk_1136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_strLitToConstructor(lean_object* v_s_1137_){
_start:
{
lean_object* v_listNil_1138_; lean_object* v_stringMk_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v_listNil_1138_ = lean_obj_once(&l_Lean_Expr_strLitToConstructor___closed__3, &l_Lean_Expr_strLitToConstructor___closed__3_once, _init_l_Lean_Expr_strLitToConstructor___closed__3);
v_stringMk_1139_ = lean_obj_once(&l_Lean_Expr_strLitToConstructor___closed__7, &l_Lean_Expr_strLitToConstructor___closed__7_once, _init_l_Lean_Expr_strLitToConstructor___closed__7);
v___x_1140_ = lean_string_data(v_s_1137_);
v___x_1141_ = l_List_foldrTR___at___00Lean_Expr_strLitToConstructor_spec__0(v_listNil_1138_, v___x_1140_);
v___x_1142_ = l_Lean_Expr_app___override(v_stringMk_1139_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_toConstructor(lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
lean_object* v_val_1144_; lean_object* v___x_1145_; 
v_val_1144_ = lean_ctor_get(v_x_1143_, 0);
lean_inc(v_val_1144_);
lean_dec_ref(v_x_1143_);
v___x_1145_ = l_Lean_Expr_natLitToConstructor(v_val_1144_);
lean_dec(v_val_1144_);
return v___x_1145_;
}
else
{
lean_object* v_val_1146_; lean_object* v___x_1147_; 
v_val_1146_ = lean_ctor_get(v_x_1143_, 0);
lean_inc_ref(v_val_1146_);
lean_dec_ref(v_x_1143_);
v___x_1147_ = l_Lean_Expr_strLitToConstructor(v_val_1146_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_typeName(lean_object* v_x_1152_){
_start:
{
if (lean_obj_tag(v_x_1152_) == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = ((lean_object*)(l_Lean_Literal_typeName___closed__0));
return v___x_1153_;
}
else
{
lean_object* v___x_1154_; 
v___x_1154_ = ((lean_object*)(l_Lean_Literal_typeName___closed__1));
return v___x_1154_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Literal_typeName___boxed(lean_object* v_x_1155_){
_start:
{
lean_object* v_res_1156_; 
v_res_1156_ = l_Lean_Literal_typeName(v_x_1155_);
lean_dec_ref(v_x_1155_);
return v_res_1156_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Expr(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Expr_prop = _init_l_Lean_Expr_prop();
lean_mark_persistent(l_Lean_Expr_prop);
l_Lean_Expr_natZero = _init_l_Lean_Expr_natZero();
lean_mark_persistent(l_Lean_Expr_natZero);
l_Lean_Expr_natSucc = _init_l_Lean_Expr_natSucc();
lean_mark_persistent(l_Lean_Expr_natSucc);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Expr(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Expr(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Expr(builtin);
}
#ifdef __cplusplus
}
#endif
