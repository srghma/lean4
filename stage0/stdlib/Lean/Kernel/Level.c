// Lean compiler output
// Module: Lean.Kernel.Level
// Imports: public import Lean public import Lean.Kernel.List
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
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Option_instBEq_beq___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_cmp(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_cmp___boxed(lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_List_reverseAux___redArg(lean_object*, lean_object*);
uint8_t l_List_compareLex___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_instReprTupleOfRepr___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec___boxed(lean_object*, lean_object*);
lean_object* l_List_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Prod_repr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_repr___redArg(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_balance___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_List_compareLex___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Level_addOffset(lean_object*, lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
uint8_t l_List_beq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasParam(lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_forEach(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_getUndefParam___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_getUndefParam___lam__0___closed__0 = (const lean_object*)&l_Lean_Level_getUndefParam___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_getUndefParam___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_forEach___at___00Lean_Level_getUndefParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_getUndefParam(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instOrdName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_cmp___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instOrdName___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instOrdName___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instOrdName = (const lean_object*)&l_Lean_Level_Normalize_instOrdName___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instBEqVarNode_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqVarNode_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instBEqVarNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instBEqVarNode_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instBEqVarNode___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instBEqVarNode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instBEqVarNode = (const lean_object*)&l_Lean_Level_Normalize_instBEqVarNode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instOrdVarNode_ord(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instOrdVarNode_ord___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instOrdVarNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instOrdVarNode_ord___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instOrdVarNode___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instOrdVarNode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instOrdVarNode = (const lean_object*)&l_Lean_Level_Normalize_instOrdVarNode___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Level_Normalize_instReprVarNode_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "var"};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__4 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__3_value),((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7;
static const lean_string_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__8 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__9 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "offset"};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__10 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__11 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__12;
static const lean_string_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__13 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__13_value;
static lean_once_cell_t l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__14;
static lean_once_cell_t l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__16 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__17 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__17_value;
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprVarNode_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instReprVarNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instReprVarNode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprVarNode___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instReprVarNode = (const lean_object*)&l_Lean_Level_Normalize_instReprVarNode___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[]"};
static const lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__0 = (const lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__0_value;
static const lean_ctor_object l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__0_value)}};
static const lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__1 = (const lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__1_value;
static const lean_string_object l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__2 = (const lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__2_value;
static const lean_ctor_object l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__9_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__3 = (const lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__3_value;
static const lean_string_object l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__4 = (const lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__4_value;
static lean_once_cell_t l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__5;
static lean_once_cell_t l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6;
static const lean_ctor_object l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__2_value)}};
static const lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__7 = (const lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__7_value;
static const lean_ctor_object l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__4_value)}};
static const lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__8 = (const lean_object*)&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__8_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1___redArg(lean_object*);
static const lean_string_object l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "path"};
static const lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__1 = (const lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__2 = (const lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__2_value),((lean_object*)&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__3 = (const lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__3_value;
static lean_once_cell_t l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__4;
static const lean_string_object l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "const"};
static const lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__5 = (const lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__6 = (const lean_object*)&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__7;
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNode_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNode_repr___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instReprNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instReprNode_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNode___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instReprNode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instReprNode = (const lean_object*)&l_Lean_Level_Normalize_instReprNode___closed__0_value;
static const lean_ctor_object l_Lean_Level_Normalize_instInhabitedNode_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Level_Normalize_instInhabitedNode_default___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instInhabitedNode_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instInhabitedNode_default = (const lean_object*)&l_Lean_Level_Normalize_instInhabitedNode_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instInhabitedNode = (const lean_object*)&l_Lean_Level_Normalize_instInhabitedNode_default___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instBEqNode___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNode___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instBEqNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instBEqNode___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instBEqVarNode___closed__0_value)} };
static const lean_object* l_Lean_Level_Normalize_instBEqNode___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instBEqNode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instBEqNode = (const lean_object*)&l_Lean_Level_Normalize_instBEqNode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instOrdNode___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instOrdNode___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instOrdNode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instOrdNode___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instOrdNode___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instOrdNode___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instOrdNode = (const lean_object*)&l_Lean_Level_Normalize_instOrdNode___closed__0_value;
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_subset___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_subset___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_subset(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_subset___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_orderedInsert___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_orderedInsert(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instReprNormLevel___aux__1___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__0_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_reprPrec___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__1 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__1_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_repr___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__1_value)} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__2 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__2_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instReprTupleOfRepr___redArg___lam__0, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNode___closed__0_value)} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__3 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__3_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Prod_repr___boxed, .m_arity = 6, .m_num_fixed = 4, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__2_value),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__3_value)} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__4 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__4_value;
static const lean_string_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Std.TreeMap.ofList "};
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__5 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__5_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__5_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__6 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__6_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__7 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__7_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__8 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__8_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__9 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__9_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__10 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__10_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__11 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__11_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__12 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__12_value;
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__13 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__13_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__7_value),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__8_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__14 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__14_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__14_value),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__9_value),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__10_value),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__11_value),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__12_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__15 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__15_value;
static const lean_ctor_object l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__15_value),((lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__13_value)}};
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__16 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__16_value;
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Level_Normalize_instReprNormLevel_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Level_Normalize_instReprNormLevel_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1_spec__2(lean_object*, lean_object*);
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__0 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__0_value;
static const lean_string_object l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__1 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__1_value;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__2;
static lean_once_cell_t l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__3;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__0_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__4 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__4_value;
static const lean_ctor_object l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__1_value)}};
static const lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__5 = (const lean_object*)&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2_spec__4_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instReprNormLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instReprNormLevel___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Level_Normalize_instReprNormLevel___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instReprNormLevel = (const lean_object*)&l_Lean_Level_Normalize_instReprNormLevel___closed__0_value;
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_List_compareLex___boxed, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Level_Normalize_instOrdName___closed__0_value)} };
static const lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1 = (const lean_object*)&l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1_value;
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instBEqNormLevel___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Level_Normalize_instBEqNormLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Level_Normalize_instBEqNormLevel___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Level_Normalize_instBEqNode___closed__0_value)} };
static const lean_object* l_Lean_Level_Normalize_instBEqNormLevel___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instBEqNormLevel___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instBEqNormLevel = (const lean_object*)&l_Lean_Level_Normalize_instBEqNormLevel___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_VarNode_addVar(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addVar_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_addVar(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_addNode(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addConst_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_addConst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_normalizeAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_subsumeVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subsumeVars_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subsumeVars_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_findParent(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_subsumption(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_subsumption___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Level_Normalize_normalize___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Level_Normalize_normalize___closed__0;
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_normalize(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_normalize___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_leVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_leVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Level_Normalize_NormLevel_le_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Level_Normalize_NormLevel_le_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_NormLevel_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_le___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_buildPaths_setPath_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths_setPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0_spec__0(lean_object*);
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Std.Data.DTreeMap.Internal.Queries"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__0_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "Std.DTreeMap.Internal.Impl.Const.get!"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__1 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__1_value;
static const lean_string_object l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Key is not present in map"};
static const lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__2 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Level_Normalize_NormLevel_buildPaths_getPath___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths_getPath___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_NormLevel_buildPaths_getPath___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths_getPath(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths_getPath___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Level_Normalize_NormLevel_buildPaths_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths(lean_object*);
static const lean_ctor_object l_Lean_Level_Normalize_instInhabitedTree_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Level_Normalize_instInhabitedTree_default___closed__0 = (const lean_object*)&l_Lean_Level_Normalize_instInhabitedTree_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instInhabitedTree_default = (const lean_object*)&l_Lean_Level_Normalize_instInhabitedTree_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Level_Normalize_instInhabitedTree = (const lean_object*)&l_Lean_Level_Normalize_instInhabitedTree_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_modifyAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_modifyAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_modify___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_toTree(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_treeVarDedup(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_treeVarDedup_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_treeVarDedup_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_reify_mkMax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_reify(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_reify_mkChild(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__4_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__4_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__6_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__6_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__List_map__unattach_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__List_map__unattach_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_mkMax_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_mkMax_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_normalize_x27(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_beq___at___00Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_beq___at___00Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all2___at___00Lean_Level_isEquivList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all2___at___00Lean_Level_isEquivList_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_isEquivList(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_isEquivList___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Level_geq_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_geq_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg___lam__1(lean_object* v_toApplicative_1_, lean_object* v_inst_2_, lean_object* v_f_3_, lean_object* v_toBind_4_, lean_object* v_l_5_, uint8_t v_____do__lift_6_){
_start:
{
lean_object* v_l_u2081_8_; lean_object* v_l_u2082_9_; 
if (v_____do__lift_6_ == 0)
{
lean_object* v_toPure_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
lean_dec(v_l_5_);
lean_dec(v_toBind_4_);
lean_dec(v_f_3_);
lean_dec_ref(v_inst_2_);
v_toPure_13_ = lean_ctor_get(v_toApplicative_1_, 1);
lean_inc(v_toPure_13_);
lean_dec_ref(v_toApplicative_1_);
v___x_14_ = lean_box(0);
v___x_15_ = lean_apply_2(v_toPure_13_, lean_box(0), v___x_14_);
return v___x_15_;
}
else
{
switch(lean_obj_tag(v_l_5_))
{
case 1:
{
lean_object* v_a_16_; lean_object* v___x_17_; 
lean_dec(v_toBind_4_);
lean_dec_ref(v_toApplicative_1_);
v_a_16_ = lean_ctor_get(v_l_5_, 0);
lean_inc(v_a_16_);
lean_dec_ref(v_l_5_);
v___x_17_ = l_Lean_Level_forEach___redArg(v_inst_2_, v_a_16_, v_f_3_);
return v___x_17_;
}
case 2:
{
lean_object* v_a_18_; lean_object* v_a_19_; 
lean_dec_ref(v_toApplicative_1_);
v_a_18_ = lean_ctor_get(v_l_5_, 0);
lean_inc(v_a_18_);
v_a_19_ = lean_ctor_get(v_l_5_, 1);
lean_inc(v_a_19_);
lean_dec_ref(v_l_5_);
v_l_u2081_8_ = v_a_18_;
v_l_u2082_9_ = v_a_19_;
goto v___jp_7_;
}
case 3:
{
lean_object* v_a_20_; lean_object* v_a_21_; 
lean_dec_ref(v_toApplicative_1_);
v_a_20_ = lean_ctor_get(v_l_5_, 0);
lean_inc(v_a_20_);
v_a_21_ = lean_ctor_get(v_l_5_, 1);
lean_inc(v_a_21_);
lean_dec_ref(v_l_5_);
v_l_u2081_8_ = v_a_20_;
v_l_u2082_9_ = v_a_21_;
goto v___jp_7_;
}
default: 
{
lean_object* v_toPure_22_; lean_object* v___x_23_; lean_object* v___x_24_; 
lean_dec(v_l_5_);
lean_dec(v_toBind_4_);
lean_dec(v_f_3_);
lean_dec_ref(v_inst_2_);
v_toPure_22_ = lean_ctor_get(v_toApplicative_1_, 1);
lean_inc(v_toPure_22_);
lean_dec_ref(v_toApplicative_1_);
v___x_23_ = lean_box(0);
v___x_24_ = lean_apply_2(v_toPure_22_, lean_box(0), v___x_23_);
return v___x_24_;
}
}
}
v___jp_7_:
{
lean_object* v___f_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
lean_inc(v_f_3_);
lean_inc_ref(v_inst_2_);
v___f_10_ = lean_alloc_closure((void*)(l_Lean_Level_forEach___redArg___lam__0), 4, 3);
lean_closure_set(v___f_10_, 0, v_inst_2_);
lean_closure_set(v___f_10_, 1, v_l_u2082_9_);
lean_closure_set(v___f_10_, 2, v_f_3_);
v___x_11_ = l_Lean_Level_forEach___redArg(v_inst_2_, v_l_u2081_8_, v_f_3_);
v___x_12_ = lean_apply_4(v_toBind_4_, lean_box(0), lean_box(0), v___x_11_, v___f_10_);
return v___x_12_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg___lam__1___boxed(lean_object* v_toApplicative_25_, lean_object* v_inst_26_, lean_object* v_f_27_, lean_object* v_toBind_28_, lean_object* v_l_29_, lean_object* v_____do__lift_30_){
_start:
{
uint8_t v_____do__lift_253__boxed_31_; lean_object* v_res_32_; 
v_____do__lift_253__boxed_31_ = lean_unbox(v_____do__lift_30_);
v_res_32_ = l_Lean_Level_forEach___redArg___lam__1(v_toApplicative_25_, v_inst_26_, v_f_27_, v_toBind_28_, v_l_29_, v_____do__lift_253__boxed_31_);
return v_res_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg(lean_object* v_inst_33_, lean_object* v_l_34_, lean_object* v_f_35_){
_start:
{
lean_object* v_toApplicative_36_; lean_object* v_toBind_37_; lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; 
v_toApplicative_36_ = lean_ctor_get(v_inst_33_, 0);
lean_inc_ref(v_toApplicative_36_);
v_toBind_37_ = lean_ctor_get(v_inst_33_, 1);
lean_inc_n(v_toBind_37_, 2);
lean_inc(v_l_34_);
lean_inc(v_f_35_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_Level_forEach___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_38_, 0, v_toApplicative_36_);
lean_closure_set(v___f_38_, 1, v_inst_33_);
lean_closure_set(v___f_38_, 2, v_f_35_);
lean_closure_set(v___f_38_, 3, v_toBind_37_);
lean_closure_set(v___f_38_, 4, v_l_34_);
v___x_39_ = lean_apply_1(v_f_35_, v_l_34_);
v___x_40_ = lean_apply_4(v_toBind_37_, lean_box(0), lean_box(0), v___x_39_, v___f_38_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_forEach___redArg___lam__0(lean_object* v_inst_41_, lean_object* v_l_u2082_42_, lean_object* v_f_43_, lean_object* v_____r_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_Lean_Level_forEach___redArg(v_inst_41_, v_l_u2082_42_, v_f_43_);
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_forEach(lean_object* v_m_46_, lean_object* v_inst_47_, lean_object* v_l_48_, lean_object* v_f_49_){
_start:
{
lean_object* v___x_50_; 
v___x_50_ = l_Lean_Level_forEach___redArg(v_inst_47_, v_l_48_, v_f_49_);
return v___x_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getUndefParam___lam__0(lean_object* v_ps_52_, lean_object* v_l_53_, lean_object* v___y_54_){
_start:
{
uint8_t v___x_59_; 
v___x_59_ = l_Lean_Level_hasParam(v_l_53_);
if (v___x_59_ == 0)
{
lean_dec(v_l_53_);
lean_dec(v_ps_52_);
goto v___jp_55_;
}
else
{
if (lean_obj_tag(v___y_54_) == 0)
{
if (lean_obj_tag(v_l_53_) == 4)
{
lean_object* v_a_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_a_60_ = lean_ctor_get(v_l_53_, 0);
lean_inc_n(v_a_60_, 2);
lean_dec_ref(v_l_53_);
v___x_61_ = ((lean_object*)(l_Lean_Level_getUndefParam___lam__0___closed__0));
v___x_62_ = l_List_elem___redArg(v___x_61_, v_a_60_, v_ps_52_);
if (v___x_62_ == 0)
{
if (v___x_59_ == 0)
{
lean_object* v___x_63_; lean_object* v___x_64_; 
lean_dec(v_a_60_);
v___x_63_ = lean_box(v___x_59_);
v___x_64_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_63_);
lean_ctor_set(v___x_64_, 1, v___y_54_);
return v___x_64_;
}
else
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_65_, 0, v_a_60_);
v___x_66_ = lean_box(v___x_59_);
v___x_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_67_, 0, v___x_66_);
lean_ctor_set(v___x_67_, 1, v___x_65_);
return v___x_67_;
}
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_dec(v_a_60_);
v___x_68_ = lean_box(v___x_59_);
v___x_69_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___y_54_);
return v___x_69_;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
lean_dec(v_l_53_);
lean_dec(v_ps_52_);
v___x_70_ = lean_box(v___x_59_);
v___x_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
lean_ctor_set(v___x_71_, 1, v___y_54_);
return v___x_71_;
}
}
else
{
lean_dec(v_l_53_);
lean_dec(v_ps_52_);
goto v___jp_55_;
}
}
v___jp_55_:
{
uint8_t v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; 
v___x_56_ = 0;
v___x_57_ = lean_box(v___x_56_);
v___x_58_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_58_, 0, v___x_57_);
lean_ctor_set(v___x_58_, 1, v___y_54_);
return v___x_58_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_forEach___at___00Lean_Level_getUndefParam_spec__0(lean_object* v_l_72_, lean_object* v_f_73_, lean_object* v___y_74_){
_start:
{
lean_object* v___x_75_; lean_object* v_fst_76_; lean_object* v_snd_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_102_; 
lean_inc_ref(v_f_73_);
lean_inc(v_l_72_);
v___x_75_ = lean_apply_2(v_f_73_, v_l_72_, v___y_74_);
v_fst_76_ = lean_ctor_get(v___x_75_, 0);
v_snd_77_ = lean_ctor_get(v___x_75_, 1);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_75_);
if (v_isSharedCheck_102_ == 0)
{
v___x_79_ = v___x_75_;
v_isShared_80_ = v_isSharedCheck_102_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_snd_77_);
lean_inc(v_fst_76_);
lean_dec(v___x_75_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_102_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v_l_u2081_82_; lean_object* v_l_u2082_83_; uint8_t v___x_87_; 
v___x_87_ = lean_unbox(v_fst_76_);
lean_dec(v_fst_76_);
if (v___x_87_ == 0)
{
lean_object* v___x_88_; lean_object* v___x_90_; 
lean_dec_ref(v_f_73_);
lean_dec(v_l_72_);
v___x_88_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_88_);
v___x_90_ = v___x_79_;
goto v_reusejp_89_;
}
else
{
lean_object* v_reuseFailAlloc_91_; 
v_reuseFailAlloc_91_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_91_, 0, v___x_88_);
lean_ctor_set(v_reuseFailAlloc_91_, 1, v_snd_77_);
v___x_90_ = v_reuseFailAlloc_91_;
goto v_reusejp_89_;
}
v_reusejp_89_:
{
return v___x_90_;
}
}
else
{
switch(lean_obj_tag(v_l_72_))
{
case 1:
{
lean_object* v_a_92_; 
lean_del_object(v___x_79_);
v_a_92_ = lean_ctor_get(v_l_72_, 0);
lean_inc(v_a_92_);
lean_dec_ref(v_l_72_);
v_l_72_ = v_a_92_;
v___y_74_ = v_snd_77_;
goto _start;
}
case 2:
{
lean_object* v_a_94_; lean_object* v_a_95_; 
lean_del_object(v___x_79_);
v_a_94_ = lean_ctor_get(v_l_72_, 0);
lean_inc(v_a_94_);
v_a_95_ = lean_ctor_get(v_l_72_, 1);
lean_inc(v_a_95_);
lean_dec_ref(v_l_72_);
v_l_u2081_82_ = v_a_94_;
v_l_u2082_83_ = v_a_95_;
goto v___jp_81_;
}
case 3:
{
lean_object* v_a_96_; lean_object* v_a_97_; 
lean_del_object(v___x_79_);
v_a_96_ = lean_ctor_get(v_l_72_, 0);
lean_inc(v_a_96_);
v_a_97_ = lean_ctor_get(v_l_72_, 1);
lean_inc(v_a_97_);
lean_dec_ref(v_l_72_);
v_l_u2081_82_ = v_a_96_;
v_l_u2082_83_ = v_a_97_;
goto v___jp_81_;
}
default: 
{
lean_object* v___x_98_; lean_object* v___x_100_; 
lean_dec_ref(v_f_73_);
lean_dec(v_l_72_);
v___x_98_ = lean_box(0);
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v___x_98_);
v___x_100_ = v___x_79_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v___x_98_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_snd_77_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
v___jp_81_:
{
lean_object* v___x_84_; lean_object* v_snd_85_; 
lean_inc_ref(v_f_73_);
v___x_84_ = l_Lean_Level_forEach___at___00Lean_Level_getUndefParam_spec__0(v_l_u2081_82_, v_f_73_, v_snd_77_);
v_snd_85_ = lean_ctor_get(v___x_84_, 1);
lean_inc(v_snd_85_);
lean_dec_ref(v___x_84_);
v_l_72_ = v_l_u2082_83_;
v___y_74_ = v_snd_85_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_getUndefParam(lean_object* v_l_103_, lean_object* v_ps_104_){
_start:
{
lean_object* v___f_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v_snd_108_; 
v___f_105_ = lean_alloc_closure((void*)(l_Lean_Level_getUndefParam___lam__0), 3, 1);
lean_closure_set(v___f_105_, 0, v_ps_104_);
v___x_106_ = lean_box(0);
v___x_107_ = l_Lean_Level_forEach___at___00Lean_Level_getUndefParam_spec__0(v_l_103_, v___f_105_, v___x_106_);
v_snd_108_ = lean_ctor_get(v___x_107_, 1);
lean_inc(v_snd_108_);
lean_dec_ref(v___x_107_);
return v_snd_108_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instBEqVarNode_beq(lean_object* v_x_111_, lean_object* v_x_112_){
_start:
{
lean_object* v_var_113_; lean_object* v_offset_114_; lean_object* v_var_115_; lean_object* v_offset_116_; uint8_t v___x_117_; 
v_var_113_ = lean_ctor_get(v_x_111_, 0);
v_offset_114_ = lean_ctor_get(v_x_111_, 1);
v_var_115_ = lean_ctor_get(v_x_112_, 0);
v_offset_116_ = lean_ctor_get(v_x_112_, 1);
v___x_117_ = lean_name_eq(v_var_113_, v_var_115_);
if (v___x_117_ == 0)
{
return v___x_117_;
}
else
{
uint8_t v___x_118_; 
v___x_118_ = lean_nat_dec_eq(v_offset_114_, v_offset_116_);
return v___x_118_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqVarNode_beq___boxed(lean_object* v_x_119_, lean_object* v_x_120_){
_start:
{
uint8_t v_res_121_; lean_object* v_r_122_; 
v_res_121_ = l_Lean_Level_Normalize_instBEqVarNode_beq(v_x_119_, v_x_120_);
lean_dec_ref(v_x_120_);
lean_dec_ref(v_x_119_);
v_r_122_ = lean_box(v_res_121_);
return v_r_122_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instOrdVarNode_ord(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
lean_object* v_var_127_; lean_object* v_offset_128_; lean_object* v_var_129_; lean_object* v_offset_130_; uint8_t v___x_131_; 
v_var_127_ = lean_ctor_get(v_x_125_, 0);
v_offset_128_ = lean_ctor_get(v_x_125_, 1);
v_var_129_ = lean_ctor_get(v_x_126_, 0);
v_offset_130_ = lean_ctor_get(v_x_126_, 1);
v___x_131_ = l_Lean_Name_cmp(v_var_127_, v_var_129_);
if (v___x_131_ == 1)
{
uint8_t v___x_132_; 
v___x_132_ = lean_nat_dec_lt(v_offset_128_, v_offset_130_);
if (v___x_132_ == 0)
{
uint8_t v___x_133_; 
v___x_133_ = lean_nat_dec_eq(v_offset_128_, v_offset_130_);
if (v___x_133_ == 0)
{
uint8_t v___x_134_; 
v___x_134_ = 2;
return v___x_134_;
}
else
{
return v___x_131_;
}
}
else
{
uint8_t v___x_135_; 
v___x_135_ = 0;
return v___x_135_;
}
}
else
{
return v___x_131_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instOrdVarNode_ord___boxed(lean_object* v_x_136_, lean_object* v_x_137_){
_start:
{
uint8_t v_res_138_; lean_object* v_r_139_; 
v_res_138_ = l_Lean_Level_Normalize_instOrdVarNode_ord(v_x_136_, v_x_137_);
lean_dec_ref(v_x_137_);
lean_dec_ref(v_x_136_);
v_r_139_ = lean_box(v_res_138_);
return v_r_139_;
}
}
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_Level_Normalize_instReprVarNode_repr_spec__0(lean_object* v_a_142_){
_start:
{
lean_object* v___x_143_; 
v___x_143_ = lean_nat_to_int(v_a_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_unsigned_to_nat(7u);
v___x_158_ = lean_nat_to_int(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_unsigned_to_nat(10u);
v___x_166_ = lean_nat_to_int(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__14(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__0));
v___x_169_ = lean_string_length(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = lean_obj_once(&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__14, &l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__14_once, _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__14);
v___x_171_ = lean_nat_to_int(v___x_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___redArg(lean_object* v_x_176_){
_start:
{
lean_object* v_var_177_; lean_object* v_offset_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_213_; 
v_var_177_ = lean_ctor_get(v_x_176_, 0);
v_offset_178_ = lean_ctor_get(v_x_176_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_176_);
if (v_isSharedCheck_213_ == 0)
{
v___x_180_ = v_x_176_;
v_isShared_181_ = v_isSharedCheck_213_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_offset_178_);
lean_inc(v_var_177_);
lean_dec(v_x_176_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_213_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_188_; 
v___x_182_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__5));
v___x_183_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__6));
v___x_184_ = lean_obj_once(&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7, &l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7_once, _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7);
v___x_185_ = lean_unsigned_to_nat(0u);
v___x_186_ = l_Lean_Name_reprPrec(v_var_177_, v___x_185_);
if (v_isShared_181_ == 0)
{
lean_ctor_set_tag(v___x_180_, 4);
lean_ctor_set(v___x_180_, 1, v___x_186_);
lean_ctor_set(v___x_180_, 0, v___x_184_);
v___x_188_ = v___x_180_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_184_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_186_);
v___x_188_ = v_reuseFailAlloc_212_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
uint8_t v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_189_ = 0;
v___x_190_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_190_, 0, v___x_188_);
lean_ctor_set_uint8(v___x_190_, sizeof(void*)*1, v___x_189_);
v___x_191_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_191_, 0, v___x_183_);
lean_ctor_set(v___x_191_, 1, v___x_190_);
v___x_192_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__9));
v___x_193_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_193_, 0, v___x_191_);
lean_ctor_set(v___x_193_, 1, v___x_192_);
v___x_194_ = lean_box(1);
v___x_195_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_195_, 0, v___x_193_);
lean_ctor_set(v___x_195_, 1, v___x_194_);
v___x_196_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__11));
v___x_197_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_197_, 0, v___x_195_);
lean_ctor_set(v___x_197_, 1, v___x_196_);
v___x_198_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v___x_182_);
v___x_199_ = lean_obj_once(&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__12, &l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__12_once, _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__12);
v___x_200_ = l_Nat_reprFast(v_offset_178_);
v___x_201_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
v___x_202_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_199_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_203_, 0, v___x_202_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*1, v___x_189_);
v___x_204_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_198_);
lean_ctor_set(v___x_204_, 1, v___x_203_);
v___x_205_ = lean_obj_once(&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15, &l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15_once, _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15);
v___x_206_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__16));
v___x_207_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_206_);
lean_ctor_set(v___x_207_, 1, v___x_204_);
v___x_208_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__17));
v___x_209_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_205_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set_uint8(v___x_211_, sizeof(void*)*1, v___x_189_);
return v___x_211_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprVarNode_repr(lean_object* v_x_214_, lean_object* v_prec_215_){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Level_Normalize_instReprVarNode_repr___redArg(v_x_214_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprVarNode_repr___boxed(lean_object* v_x_217_, lean_object* v_prec_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_Level_Normalize_instReprVarNode_repr(v_x_217_, v_prec_218_);
lean_dec(v_prec_218_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0___lam__0(lean_object* v___y_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; 
v___x_223_ = lean_unsigned_to_nat(0u);
v___x_224_ = l_Lean_Name_reprPrec(v___y_222_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0_spec__1_spec__3(lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_x_227_){
_start:
{
if (lean_obj_tag(v_x_227_) == 0)
{
lean_dec(v_x_225_);
return v_x_226_;
}
else
{
lean_object* v_head_228_; lean_object* v_tail_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_240_; 
v_head_228_ = lean_ctor_get(v_x_227_, 0);
v_tail_229_ = lean_ctor_get(v_x_227_, 1);
v_isSharedCheck_240_ = !lean_is_exclusive(v_x_227_);
if (v_isSharedCheck_240_ == 0)
{
v___x_231_ = v_x_227_;
v_isShared_232_ = v_isSharedCheck_240_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_tail_229_);
lean_inc(v_head_228_);
lean_dec(v_x_227_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_240_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_234_; 
lean_inc(v_x_225_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 5);
lean_ctor_set(v___x_231_, 1, v_x_225_);
lean_ctor_set(v___x_231_, 0, v_x_226_);
v___x_234_ = v___x_231_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_x_226_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v_x_225_);
v___x_234_ = v_reuseFailAlloc_239_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = lean_unsigned_to_nat(0u);
v___x_236_ = l_Lean_Name_reprPrec(v_head_228_, v___x_235_);
v___x_237_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_237_, 0, v___x_234_);
lean_ctor_set(v___x_237_, 1, v___x_236_);
v_x_226_ = v___x_237_;
v_x_227_ = v_tail_229_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0_spec__1(lean_object* v_x_241_, lean_object* v_x_242_, lean_object* v_x_243_){
_start:
{
if (lean_obj_tag(v_x_243_) == 0)
{
lean_dec(v_x_241_);
return v_x_242_;
}
else
{
lean_object* v_head_244_; lean_object* v_tail_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_256_; 
v_head_244_ = lean_ctor_get(v_x_243_, 0);
v_tail_245_ = lean_ctor_get(v_x_243_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_243_);
if (v_isSharedCheck_256_ == 0)
{
v___x_247_ = v_x_243_;
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_tail_245_);
lean_inc(v_head_244_);
lean_dec(v_x_243_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_256_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
lean_inc(v_x_241_);
if (v_isShared_248_ == 0)
{
lean_ctor_set_tag(v___x_247_, 5);
lean_ctor_set(v___x_247_, 1, v_x_241_);
lean_ctor_set(v___x_247_, 0, v_x_242_);
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_x_242_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_x_241_);
v___x_250_ = v_reuseFailAlloc_255_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_251_ = lean_unsigned_to_nat(0u);
v___x_252_ = l_Lean_Name_reprPrec(v_head_244_, v___x_251_);
v___x_253_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_250_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0_spec__1_spec__3(v_x_241_, v___x_253_, v_tail_245_);
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0(lean_object* v_x_257_, lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
lean_object* v___x_259_; 
lean_dec(v_x_258_);
v___x_259_ = lean_box(0);
return v___x_259_;
}
else
{
lean_object* v_tail_260_; 
v_tail_260_ = lean_ctor_get(v_x_257_, 1);
if (lean_obj_tag(v_tail_260_) == 0)
{
lean_object* v_head_261_; lean_object* v___x_262_; 
lean_dec(v_x_258_);
v_head_261_ = lean_ctor_get(v_x_257_, 0);
lean_inc(v_head_261_);
lean_dec_ref(v_x_257_);
v___x_262_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0___lam__0(v_head_261_);
return v___x_262_;
}
else
{
lean_object* v_head_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_inc(v_tail_260_);
v_head_263_ = lean_ctor_get(v_x_257_, 0);
lean_inc(v_head_263_);
lean_dec_ref(v_x_257_);
v___x_264_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0___lam__0(v_head_263_);
v___x_265_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0_spec__1(v_x_258_, v___x_264_, v_tail_260_);
return v___x_265_;
}
}
}
}
static lean_object* _init_l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__5(void){
_start:
{
lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_274_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__2));
v___x_275_ = lean_string_length(v___x_274_);
return v___x_275_;
}
}
static lean_object* _init_l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = lean_obj_once(&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__5, &l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__5_once, _init_l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__5);
v___x_277_ = lean_nat_to_int(v___x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg(lean_object* v_a_282_){
_start:
{
if (lean_obj_tag(v_a_282_) == 0)
{
lean_object* v___x_283_; 
v___x_283_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__1));
return v___x_283_;
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; 
v___x_284_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__3));
v___x_285_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0_spec__0(v_a_282_, v___x_284_);
v___x_286_ = lean_obj_once(&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6, &l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6_once, _init_l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6);
v___x_287_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__7));
v___x_288_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_287_);
lean_ctor_set(v___x_288_, 1, v___x_285_);
v___x_289_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__8));
v___x_290_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_290_, 0, v___x_288_);
lean_ctor_set(v___x_290_, 1, v___x_289_);
v___x_291_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_291_, 0, v___x_286_);
lean_ctor_set(v___x_291_, 1, v___x_290_);
v___x_292_ = 0;
v___x_293_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_293_, 0, v___x_291_);
lean_ctor_set_uint8(v___x_293_, sizeof(void*)*1, v___x_292_);
return v___x_293_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
if (lean_obj_tag(v_x_296_) == 0)
{
lean_dec(v_x_294_);
return v_x_295_;
}
else
{
lean_object* v_head_297_; lean_object* v_tail_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_308_; 
v_head_297_ = lean_ctor_get(v_x_296_, 0);
v_tail_298_ = lean_ctor_get(v_x_296_, 1);
v_isSharedCheck_308_ = !lean_is_exclusive(v_x_296_);
if (v_isSharedCheck_308_ == 0)
{
v___x_300_ = v_x_296_;
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_tail_298_);
lean_inc(v_head_297_);
lean_dec(v_x_296_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_308_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
lean_inc(v_x_294_);
if (v_isShared_301_ == 0)
{
lean_ctor_set_tag(v___x_300_, 5);
lean_ctor_set(v___x_300_, 1, v_x_294_);
lean_ctor_set(v___x_300_, 0, v_x_295_);
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_x_295_);
lean_ctor_set(v_reuseFailAlloc_307_, 1, v_x_294_);
v___x_303_ = v_reuseFailAlloc_307_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
lean_object* v___x_304_; lean_object* v___x_305_; 
v___x_304_ = l_Lean_Level_Normalize_instReprVarNode_repr___redArg(v_head_297_);
v___x_305_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_305_, 0, v___x_303_);
lean_ctor_set(v___x_305_, 1, v___x_304_);
v_x_295_ = v___x_305_;
v_x_296_ = v_tail_298_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2_spec__4(lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
if (lean_obj_tag(v_x_311_) == 0)
{
lean_dec(v_x_309_);
return v_x_310_;
}
else
{
lean_object* v_head_312_; lean_object* v_tail_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_323_; 
v_head_312_ = lean_ctor_get(v_x_311_, 0);
v_tail_313_ = lean_ctor_get(v_x_311_, 1);
v_isSharedCheck_323_ = !lean_is_exclusive(v_x_311_);
if (v_isSharedCheck_323_ == 0)
{
v___x_315_ = v_x_311_;
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_tail_313_);
lean_inc(v_head_312_);
lean_dec(v_x_311_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_323_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
lean_inc(v_x_309_);
if (v_isShared_316_ == 0)
{
lean_ctor_set_tag(v___x_315_, 5);
lean_ctor_set(v___x_315_, 1, v_x_309_);
lean_ctor_set(v___x_315_, 0, v_x_310_);
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_322_; 
v_reuseFailAlloc_322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_322_, 0, v_x_310_);
lean_ctor_set(v_reuseFailAlloc_322_, 1, v_x_309_);
v___x_318_ = v_reuseFailAlloc_322_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_319_ = l_Lean_Level_Normalize_instReprVarNode_repr___redArg(v_head_312_);
v___x_320_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_318_);
lean_ctor_set(v___x_320_, 1, v___x_319_);
v___x_321_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2_spec__4_spec__6(v_x_309_, v___x_320_, v_tail_313_);
return v___x_321_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2(lean_object* v_x_324_, lean_object* v_x_325_){
_start:
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v___x_326_; 
lean_dec(v_x_325_);
v___x_326_ = lean_box(0);
return v___x_326_;
}
else
{
lean_object* v_tail_327_; 
v_tail_327_ = lean_ctor_get(v_x_324_, 1);
if (lean_obj_tag(v_tail_327_) == 0)
{
lean_object* v_head_328_; lean_object* v___x_329_; 
lean_dec(v_x_325_);
v_head_328_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_head_328_);
lean_dec_ref(v_x_324_);
v___x_329_ = l_Lean_Level_Normalize_instReprVarNode_repr___redArg(v_head_328_);
return v___x_329_;
}
else
{
lean_object* v_head_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
lean_inc(v_tail_327_);
v_head_330_ = lean_ctor_get(v_x_324_, 0);
lean_inc(v_head_330_);
lean_dec_ref(v_x_324_);
v___x_331_ = l_Lean_Level_Normalize_instReprVarNode_repr___redArg(v_head_330_);
v___x_332_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2_spec__4(v_x_325_, v___x_331_, v_tail_327_);
return v___x_332_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1___redArg(lean_object* v_a_333_){
_start:
{
if (lean_obj_tag(v_a_333_) == 0)
{
lean_object* v___x_334_; 
v___x_334_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__1));
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; uint8_t v___x_343_; lean_object* v___x_344_; 
v___x_335_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__3));
v___x_336_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1_spec__2(v_a_333_, v___x_335_);
v___x_337_ = lean_obj_once(&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6, &l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6_once, _init_l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6);
v___x_338_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__7));
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v___x_336_);
v___x_340_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__8));
v___x_341_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_341_, 0, v___x_339_);
lean_ctor_set(v___x_341_, 1, v___x_340_);
v___x_342_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_337_);
lean_ctor_set(v___x_342_, 1, v___x_341_);
v___x_343_ = 0;
v___x_344_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set_uint8(v___x_344_, sizeof(void*)*1, v___x_343_);
return v___x_344_;
}
}
}
static lean_object* _init_l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__4(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = lean_unsigned_to_nat(8u);
v___x_355_ = lean_nat_to_int(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = lean_unsigned_to_nat(9u);
v___x_360_ = lean_nat_to_int(v___x_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNode_repr___redArg(lean_object* v_x_361_){
_start:
{
lean_object* v_path_362_; lean_object* v_const_363_; lean_object* v_var_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; uint8_t v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; 
v_path_362_ = lean_ctor_get(v_x_361_, 0);
lean_inc(v_path_362_);
v_const_363_ = lean_ctor_get(v_x_361_, 1);
lean_inc(v_const_363_);
v_var_364_ = lean_ctor_get(v_x_361_, 2);
lean_inc(v_var_364_);
lean_dec_ref(v_x_361_);
v___x_365_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__5));
v___x_366_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__3));
v___x_367_ = lean_obj_once(&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__4, &l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__4_once, _init_l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__4);
v___x_368_ = l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg(v_path_362_);
v___x_369_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_367_);
lean_ctor_set(v___x_369_, 1, v___x_368_);
v___x_370_ = 0;
v___x_371_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_371_, 0, v___x_369_);
lean_ctor_set_uint8(v___x_371_, sizeof(void*)*1, v___x_370_);
v___x_372_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_366_);
lean_ctor_set(v___x_372_, 1, v___x_371_);
v___x_373_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__9));
v___x_374_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_372_);
lean_ctor_set(v___x_374_, 1, v___x_373_);
v___x_375_ = lean_box(1);
v___x_376_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__6));
v___x_378_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_378_, 0, v___x_376_);
lean_ctor_set(v___x_378_, 1, v___x_377_);
v___x_379_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v___x_365_);
v___x_380_ = lean_obj_once(&l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__7, &l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__7_once, _init_l_Lean_Level_Normalize_instReprNode_repr___redArg___closed__7);
v___x_381_ = l_Nat_reprFast(v_const_363_);
v___x_382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_382_, 0, v___x_381_);
v___x_383_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_380_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v___x_384_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_384_, 0, v___x_383_);
lean_ctor_set_uint8(v___x_384_, sizeof(void*)*1, v___x_370_);
v___x_385_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_379_);
lean_ctor_set(v___x_385_, 1, v___x_384_);
v___x_386_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_386_, 0, v___x_385_);
lean_ctor_set(v___x_386_, 1, v___x_373_);
v___x_387_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_387_, 0, v___x_386_);
lean_ctor_set(v___x_387_, 1, v___x_375_);
v___x_388_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__2));
v___x_389_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_389_, 0, v___x_387_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v___x_390_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_390_, 0, v___x_389_);
lean_ctor_set(v___x_390_, 1, v___x_365_);
v___x_391_ = lean_obj_once(&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7, &l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7_once, _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__7);
v___x_392_ = l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1___redArg(v_var_364_);
v___x_393_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_391_);
lean_ctor_set(v___x_393_, 1, v___x_392_);
v___x_394_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_394_, 0, v___x_393_);
lean_ctor_set_uint8(v___x_394_, sizeof(void*)*1, v___x_370_);
v___x_395_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_395_, 0, v___x_390_);
lean_ctor_set(v___x_395_, 1, v___x_394_);
v___x_396_ = lean_obj_once(&l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15, &l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15_once, _init_l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__15);
v___x_397_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__16));
v___x_398_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v___x_395_);
v___x_399_ = ((lean_object*)(l_Lean_Level_Normalize_instReprVarNode_repr___redArg___closed__17));
v___x_400_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_400_, 0, v___x_398_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
v___x_401_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_401_, 0, v___x_396_);
lean_ctor_set(v___x_401_, 1, v___x_400_);
v___x_402_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_402_, 0, v___x_401_);
lean_ctor_set_uint8(v___x_402_, sizeof(void*)*1, v___x_370_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNode_repr(lean_object* v_x_403_, lean_object* v_prec_404_){
_start:
{
lean_object* v___x_405_; 
v___x_405_ = l_Lean_Level_Normalize_instReprNode_repr___redArg(v_x_403_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNode_repr___boxed(lean_object* v_x_406_, lean_object* v_prec_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_Lean_Level_Normalize_instReprNode_repr(v_x_406_, v_prec_407_);
lean_dec(v_prec_407_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0(lean_object* v_a_409_, lean_object* v_n_410_){
_start:
{
lean_object* v___x_411_; 
v___x_411_ = l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg(v_a_409_);
return v___x_411_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___boxed(lean_object* v_a_412_, lean_object* v_n_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0(v_a_412_, v_n_413_);
lean_dec(v_n_413_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1(lean_object* v_a_415_, lean_object* v_n_416_){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1___redArg(v_a_415_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1___boxed(lean_object* v_a_418_, lean_object* v_n_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__1(v_a_418_, v_n_419_);
lean_dec(v_n_419_);
return v_res_420_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instBEqNode___lam__0(lean_object* v___x_428_, lean_object* v_n_u2081_429_, lean_object* v_n_u2082_430_){
_start:
{
lean_object* v_const_431_; lean_object* v_var_432_; lean_object* v_const_433_; lean_object* v_var_434_; uint8_t v___x_435_; 
v_const_431_ = lean_ctor_get(v_n_u2081_429_, 1);
lean_inc(v_const_431_);
v_var_432_ = lean_ctor_get(v_n_u2081_429_, 2);
lean_inc(v_var_432_);
lean_dec_ref(v_n_u2081_429_);
v_const_433_ = lean_ctor_get(v_n_u2082_430_, 1);
lean_inc(v_const_433_);
v_var_434_ = lean_ctor_get(v_n_u2082_430_, 2);
lean_inc(v_var_434_);
lean_dec_ref(v_n_u2082_430_);
v___x_435_ = lean_nat_dec_eq(v_const_431_, v_const_433_);
lean_dec(v_const_433_);
lean_dec(v_const_431_);
if (v___x_435_ == 0)
{
lean_dec(v_var_434_);
lean_dec(v_var_432_);
lean_dec_ref(v___x_428_);
return v___x_435_;
}
else
{
uint8_t v___x_436_; 
v___x_436_ = l_List_beq___redArg(v___x_428_, v_var_432_, v_var_434_);
return v___x_436_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNode___lam__0___boxed(lean_object* v___x_437_, lean_object* v_n_u2081_438_, lean_object* v_n_u2082_439_){
_start:
{
uint8_t v_res_440_; lean_object* v_r_441_; 
v_res_440_ = l_Lean_Level_Normalize_instBEqNode___lam__0(v___x_437_, v_n_u2081_438_, v_n_u2082_439_);
v_r_441_ = lean_box(v_res_440_);
return v_r_441_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instOrdNode___lam__0(lean_object* v_n_u2081_445_, lean_object* v_n_u2082_446_){
_start:
{
lean_object* v_const_447_; lean_object* v_var_448_; lean_object* v_const_449_; lean_object* v_var_450_; uint8_t v___x_451_; 
v_const_447_ = lean_ctor_get(v_n_u2081_445_, 1);
lean_inc(v_const_447_);
v_var_448_ = lean_ctor_get(v_n_u2081_445_, 2);
lean_inc(v_var_448_);
lean_dec_ref(v_n_u2081_445_);
v_const_449_ = lean_ctor_get(v_n_u2082_446_, 1);
lean_inc(v_const_449_);
v_var_450_ = lean_ctor_get(v_n_u2082_446_, 2);
lean_inc(v_var_450_);
lean_dec_ref(v_n_u2082_446_);
v___x_451_ = lean_nat_dec_lt(v_const_447_, v_const_449_);
if (v___x_451_ == 0)
{
uint8_t v___x_452_; 
v___x_452_ = lean_nat_dec_eq(v_const_447_, v_const_449_);
lean_dec(v_const_449_);
lean_dec(v_const_447_);
if (v___x_452_ == 0)
{
uint8_t v___x_453_; 
lean_dec(v_var_450_);
lean_dec(v_var_448_);
v___x_453_ = 2;
return v___x_453_;
}
else
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = ((lean_object*)(l_Lean_Level_Normalize_instOrdVarNode___closed__0));
v___x_455_ = l_List_compareLex___redArg(v___x_454_, v_var_448_, v_var_450_);
return v___x_455_;
}
}
else
{
uint8_t v___x_456_; 
lean_dec(v_var_450_);
lean_dec(v_const_449_);
lean_dec(v_var_448_);
lean_dec(v_const_447_);
v___x_456_ = 0;
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instOrdNode___lam__0___boxed(lean_object* v_n_u2081_457_, lean_object* v_n_u2082_458_){
_start:
{
uint8_t v_res_459_; lean_object* v_r_460_; 
v_res_459_ = l_Lean_Level_Normalize_instOrdNode___lam__0(v_n_u2081_457_, v_n_u2082_458_);
v_r_460_ = lean_box(v_res_459_);
return v_r_460_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_subset___redArg(lean_object* v_cmp_463_, lean_object* v_x_464_, lean_object* v_x_465_){
_start:
{
if (lean_obj_tag(v_x_464_) == 0)
{
uint8_t v___x_466_; 
lean_dec(v_x_465_);
lean_dec_ref(v_cmp_463_);
v___x_466_ = 1;
return v___x_466_;
}
else
{
if (lean_obj_tag(v_x_465_) == 0)
{
uint8_t v___x_467_; 
lean_dec_ref(v_x_464_);
lean_dec_ref(v_cmp_463_);
v___x_467_ = 0;
return v___x_467_;
}
else
{
lean_object* v_head_468_; lean_object* v_tail_469_; lean_object* v_head_470_; lean_object* v_tail_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v_head_468_ = lean_ctor_get(v_x_464_, 0);
v_tail_469_ = lean_ctor_get(v_x_464_, 1);
v_head_470_ = lean_ctor_get(v_x_465_, 0);
lean_inc(v_head_470_);
v_tail_471_ = lean_ctor_get(v_x_465_, 1);
lean_inc(v_tail_471_);
lean_dec_ref(v_x_465_);
lean_inc_ref(v_cmp_463_);
lean_inc(v_head_468_);
v___x_472_ = lean_apply_2(v_cmp_463_, v_head_468_, v_head_470_);
v___x_473_ = lean_unbox(v___x_472_);
switch(v___x_473_)
{
case 0:
{
uint8_t v___x_474_; 
lean_dec(v_tail_471_);
lean_dec_ref(v_x_464_);
lean_dec_ref(v_cmp_463_);
v___x_474_ = 0;
return v___x_474_;
}
case 1:
{
lean_inc(v_tail_469_);
lean_dec_ref(v_x_464_);
v_x_464_ = v_tail_469_;
v_x_465_ = v_tail_471_;
goto _start;
}
default: 
{
v_x_465_ = v_tail_471_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_subset___redArg___boxed(lean_object* v_cmp_477_, lean_object* v_x_478_, lean_object* v_x_479_){
_start:
{
uint8_t v_res_480_; lean_object* v_r_481_; 
v_res_480_ = l_Lean_Level_Normalize_subset___redArg(v_cmp_477_, v_x_478_, v_x_479_);
v_r_481_ = lean_box(v_res_480_);
return v_r_481_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_subset(lean_object* v_00_u03b1_482_, lean_object* v_cmp_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
uint8_t v___x_486_; 
v___x_486_ = l_Lean_Level_Normalize_subset___redArg(v_cmp_483_, v_x_484_, v_x_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_subset___boxed(lean_object* v_00_u03b1_487_, lean_object* v_cmp_488_, lean_object* v_x_489_, lean_object* v_x_490_){
_start:
{
uint8_t v_res_491_; lean_object* v_r_492_; 
v_res_491_ = l_Lean_Level_Normalize_subset(v_00_u03b1_487_, v_cmp_488_, v_x_489_, v_x_490_);
v_r_492_ = lean_box(v_res_491_);
return v_r_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_orderedInsert___redArg(lean_object* v_cmp_493_, lean_object* v_a_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref(v_cmp_493_);
v___x_496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_496_, 0, v_a_494_);
lean_ctor_set(v___x_496_, 1, v_x_495_);
v___x_497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_497_, 0, v___x_496_);
return v___x_497_;
}
else
{
lean_object* v_head_498_; lean_object* v_tail_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
v_head_498_ = lean_ctor_get(v_x_495_, 0);
v_tail_499_ = lean_ctor_get(v_x_495_, 1);
lean_inc_ref(v_cmp_493_);
lean_inc(v_head_498_);
lean_inc(v_a_494_);
v___x_500_ = lean_apply_2(v_cmp_493_, v_a_494_, v_head_498_);
v___x_501_ = lean_unbox(v___x_500_);
switch(v___x_501_)
{
case 0:
{
lean_object* v___x_502_; lean_object* v___x_503_; 
lean_dec_ref(v_cmp_493_);
v___x_502_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_502_, 0, v_a_494_);
lean_ctor_set(v___x_502_, 1, v_x_495_);
v___x_503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_503_, 0, v___x_502_);
return v___x_503_;
}
case 1:
{
lean_object* v___x_504_; 
lean_dec_ref(v_x_495_);
lean_dec(v_a_494_);
lean_dec_ref(v_cmp_493_);
v___x_504_ = lean_box(0);
return v___x_504_;
}
default: 
{
lean_object* v___x_506_; uint8_t v_isShared_507_; uint8_t v_isSharedCheck_520_; 
lean_inc(v_tail_499_);
lean_inc(v_head_498_);
v_isSharedCheck_520_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; lean_object* v_unused_522_; 
v_unused_521_ = lean_ctor_get(v_x_495_, 1);
lean_dec(v_unused_521_);
v_unused_522_ = lean_ctor_get(v_x_495_, 0);
lean_dec(v_unused_522_);
v___x_506_ = v_x_495_;
v_isShared_507_ = v_isSharedCheck_520_;
goto v_resetjp_505_;
}
else
{
lean_dec(v_x_495_);
v___x_506_ = lean_box(0);
v_isShared_507_ = v_isSharedCheck_520_;
goto v_resetjp_505_;
}
v_resetjp_505_:
{
lean_object* v___x_508_; 
v___x_508_ = l_Lean_Level_Normalize_orderedInsert___redArg(v_cmp_493_, v_a_494_, v_tail_499_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_del_object(v___x_506_);
lean_dec(v_head_498_);
return v___x_508_;
}
else
{
lean_object* v_val_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_519_; 
v_val_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_519_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_519_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_519_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_val_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_519_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_514_; 
if (v_isShared_507_ == 0)
{
lean_ctor_set(v___x_506_, 1, v_val_509_);
v___x_514_ = v___x_506_;
goto v_reusejp_513_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v_head_498_);
lean_ctor_set(v_reuseFailAlloc_518_, 1, v_val_509_);
v___x_514_ = v_reuseFailAlloc_518_;
goto v_reusejp_513_;
}
v_reusejp_513_:
{
lean_object* v___x_516_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_514_);
v___x_516_ = v___x_511_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v___x_514_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
return v___x_516_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_orderedInsert(lean_object* v_00_u03b1_523_, lean_object* v_cmp_524_, lean_object* v_a_525_, lean_object* v_x_526_){
_start:
{
lean_object* v___x_527_; 
v___x_527_ = l_Lean_Level_Normalize_orderedInsert___redArg(v_cmp_524_, v_a_525_, v_x_526_);
return v___x_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___lam__0(lean_object* v_x1_528_, lean_object* v_x2_529_, lean_object* v_x3_530_){
_start:
{
lean_object* v___x_531_; lean_object* v___x_532_; 
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_x1_528_);
lean_ctor_set(v___x_531_, 1, v_x2_529_);
v___x_532_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
lean_ctor_set(v___x_532_, 1, v_x3_530_);
return v___x_532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1(lean_object* v_m_564_, lean_object* v_prec_565_){
_start:
{
lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v___f_566_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__0));
v___x_567_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__4));
v___x_568_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__6));
v___x_569_ = lean_box(0);
v___x_570_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__16));
v___x_571_ = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(v___x_570_, v___f_566_, v___x_569_, v_m_564_);
v___x_572_ = l_List_repr___redArg(v___x_567_, v___x_571_);
v___x_573_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_573_, 0, v___x_568_);
lean_ctor_set(v___x_573_, 1, v___x_572_);
v___x_574_ = l_Repr_addAppParen(v___x_573_, v_prec_565_);
return v___x_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___aux__1___boxed(lean_object* v_m_575_, lean_object* v_prec_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Level_Normalize_instReprNormLevel___aux__1(v_m_575_, v_prec_576_);
lean_dec(v_prec_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Level_Normalize_instReprNormLevel_spec__0(lean_object* v_init_578_, lean_object* v_x_579_){
_start:
{
if (lean_obj_tag(v_x_579_) == 0)
{
lean_object* v_k_580_; lean_object* v_v_581_; lean_object* v_l_582_; lean_object* v_r_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; 
v_k_580_ = lean_ctor_get(v_x_579_, 1);
v_v_581_ = lean_ctor_get(v_x_579_, 2);
v_l_582_ = lean_ctor_get(v_x_579_, 3);
v_r_583_ = lean_ctor_get(v_x_579_, 4);
v___x_584_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Level_Normalize_instReprNormLevel_spec__0(v_init_578_, v_r_583_);
lean_inc(v_v_581_);
lean_inc(v_k_580_);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_k_580_);
lean_ctor_set(v___x_585_, 1, v_v_581_);
v___x_586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_585_);
lean_ctor_set(v___x_586_, 1, v___x_584_);
v_init_578_ = v___x_586_;
v_x_579_ = v_l_582_;
goto _start;
}
else
{
return v_init_578_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Level_Normalize_instReprNormLevel_spec__0___boxed(lean_object* v_init_588_, lean_object* v_x_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Level_Normalize_instReprNormLevel_spec__0(v_init_588_, v_x_589_);
lean_dec(v_x_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1_spec__2_spec__3(lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
if (lean_obj_tag(v_x_593_) == 0)
{
lean_dec(v_x_591_);
return v_x_592_;
}
else
{
lean_object* v_head_594_; lean_object* v_tail_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_604_; 
v_head_594_ = lean_ctor_get(v_x_593_, 0);
v_tail_595_ = lean_ctor_get(v_x_593_, 1);
v_isSharedCheck_604_ = !lean_is_exclusive(v_x_593_);
if (v_isSharedCheck_604_ == 0)
{
v___x_597_ = v_x_593_;
v_isShared_598_ = v_isSharedCheck_604_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_tail_595_);
lean_inc(v_head_594_);
lean_dec(v_x_593_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_604_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
lean_object* v___x_600_; 
lean_inc(v_x_591_);
if (v_isShared_598_ == 0)
{
lean_ctor_set_tag(v___x_597_, 5);
lean_ctor_set(v___x_597_, 1, v_x_591_);
lean_ctor_set(v___x_597_, 0, v_x_592_);
v___x_600_ = v___x_597_;
goto v_reusejp_599_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_x_592_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_x_591_);
v___x_600_ = v_reuseFailAlloc_603_;
goto v_reusejp_599_;
}
v_reusejp_599_:
{
lean_object* v___x_601_; 
v___x_601_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_600_);
lean_ctor_set(v___x_601_, 1, v_head_594_);
v_x_592_ = v___x_601_;
v_x_593_ = v_tail_595_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1_spec__2(lean_object* v_x_605_, lean_object* v_x_606_){
_start:
{
if (lean_obj_tag(v_x_605_) == 0)
{
lean_object* v___x_607_; 
lean_dec(v_x_606_);
v___x_607_ = lean_box(0);
return v___x_607_;
}
else
{
lean_object* v_tail_608_; 
v_tail_608_ = lean_ctor_get(v_x_605_, 1);
if (lean_obj_tag(v_tail_608_) == 0)
{
lean_object* v_head_609_; 
lean_dec(v_x_606_);
v_head_609_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_head_609_);
lean_dec_ref(v_x_605_);
return v_head_609_;
}
else
{
lean_object* v_head_610_; lean_object* v___x_611_; 
lean_inc(v_tail_608_);
v_head_610_ = lean_ctor_get(v_x_605_, 0);
lean_inc(v_head_610_);
lean_dec_ref(v_x_605_);
v___x_611_ = l_List_foldl___at___00Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1_spec__2_spec__3(v_x_606_, v_head_610_, v_tail_608_);
return v___x_611_;
}
}
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__2(void){
_start:
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__0));
v___x_615_ = lean_string_length(v___x_614_);
return v___x_615_;
}
}
static lean_object* _init_l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__2, &l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__2_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__2);
v___x_617_ = lean_nat_to_int(v___x_616_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg(lean_object* v_x_622_){
_start:
{
lean_object* v_fst_623_; lean_object* v_snd_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_646_; 
v_fst_623_ = lean_ctor_get(v_x_622_, 0);
v_snd_624_ = lean_ctor_get(v_x_622_, 1);
v_isSharedCheck_646_ = !lean_is_exclusive(v_x_622_);
if (v_isSharedCheck_646_ == 0)
{
v___x_626_ = v_x_622_;
v_isShared_627_ = v_isSharedCheck_646_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_snd_624_);
lean_inc(v_fst_623_);
lean_dec(v_x_622_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_646_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_628_ = l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg(v_fst_623_);
v___x_629_ = lean_box(0);
if (v_isShared_627_ == 0)
{
lean_ctor_set_tag(v___x_626_, 1);
lean_ctor_set(v___x_626_, 1, v___x_629_);
lean_ctor_set(v___x_626_, 0, v___x_628_);
v___x_631_ = v___x_626_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_628_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v___x_629_);
v___x_631_ = v_reuseFailAlloc_645_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; lean_object* v___x_644_; 
v___x_632_ = l_Lean_Level_Normalize_instReprNode_repr___redArg(v_snd_624_);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
v___x_634_ = l_List_reverse___redArg(v___x_633_);
v___x_635_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__3));
v___x_636_ = l_Std_Format_joinSep___at___00Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1_spec__2(v___x_634_, v___x_635_);
v___x_637_ = lean_obj_once(&l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__3, &l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__3_once, _init_l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__3);
v___x_638_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__4));
v___x_639_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v___x_636_);
v___x_640_ = ((lean_object*)(l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg___closed__5));
v___x_641_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
v___x_642_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_642_, 0, v___x_637_);
lean_ctor_set(v___x_642_, 1, v___x_641_);
v___x_643_ = 0;
v___x_644_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_644_, 0, v___x_642_);
lean_ctor_set_uint8(v___x_644_, sizeof(void*)*1, v___x_643_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2_spec__4_spec__6(lean_object* v_x_647_, lean_object* v_x_648_, lean_object* v_x_649_){
_start:
{
if (lean_obj_tag(v_x_649_) == 0)
{
lean_dec(v_x_647_);
return v_x_648_;
}
else
{
lean_object* v_head_650_; lean_object* v_tail_651_; lean_object* v___x_653_; uint8_t v_isShared_654_; uint8_t v_isSharedCheck_661_; 
v_head_650_ = lean_ctor_get(v_x_649_, 0);
v_tail_651_ = lean_ctor_get(v_x_649_, 1);
v_isSharedCheck_661_ = !lean_is_exclusive(v_x_649_);
if (v_isSharedCheck_661_ == 0)
{
v___x_653_ = v_x_649_;
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
else
{
lean_inc(v_tail_651_);
lean_inc(v_head_650_);
lean_dec(v_x_649_);
v___x_653_ = lean_box(0);
v_isShared_654_ = v_isSharedCheck_661_;
goto v_resetjp_652_;
}
v_resetjp_652_:
{
lean_object* v___x_656_; 
lean_inc(v_x_647_);
if (v_isShared_654_ == 0)
{
lean_ctor_set_tag(v___x_653_, 5);
lean_ctor_set(v___x_653_, 1, v_x_647_);
lean_ctor_set(v___x_653_, 0, v_x_648_);
v___x_656_ = v___x_653_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_660_; 
v_reuseFailAlloc_660_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_660_, 0, v_x_648_);
lean_ctor_set(v_reuseFailAlloc_660_, 1, v_x_647_);
v___x_656_ = v_reuseFailAlloc_660_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_657_ = l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg(v_head_650_);
v___x_658_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_656_);
lean_ctor_set(v___x_658_, 1, v___x_657_);
v_x_648_ = v___x_658_;
v_x_649_ = v_tail_651_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2_spec__4(lean_object* v_x_662_, lean_object* v_x_663_, lean_object* v_x_664_){
_start:
{
if (lean_obj_tag(v_x_664_) == 0)
{
lean_dec(v_x_662_);
return v_x_663_;
}
else
{
lean_object* v_head_665_; lean_object* v_tail_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_676_; 
v_head_665_ = lean_ctor_get(v_x_664_, 0);
v_tail_666_ = lean_ctor_get(v_x_664_, 1);
v_isSharedCheck_676_ = !lean_is_exclusive(v_x_664_);
if (v_isSharedCheck_676_ == 0)
{
v___x_668_ = v_x_664_;
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_tail_666_);
lean_inc(v_head_665_);
lean_dec(v_x_664_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_676_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
lean_inc(v_x_662_);
if (v_isShared_669_ == 0)
{
lean_ctor_set_tag(v___x_668_, 5);
lean_ctor_set(v___x_668_, 1, v_x_662_);
lean_ctor_set(v___x_668_, 0, v_x_663_);
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_675_; 
v_reuseFailAlloc_675_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_675_, 0, v_x_663_);
lean_ctor_set(v_reuseFailAlloc_675_, 1, v_x_662_);
v___x_671_ = v_reuseFailAlloc_675_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg(v_head_665_);
v___x_673_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_673_, 0, v___x_671_);
lean_ctor_set(v___x_673_, 1, v___x_672_);
v___x_674_ = l_List_foldl___at___00List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2_spec__4_spec__6(v_x_662_, v___x_673_, v_tail_666_);
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2(lean_object* v_x_677_, lean_object* v_x_678_){
_start:
{
if (lean_obj_tag(v_x_677_) == 0)
{
lean_object* v___x_679_; 
lean_dec(v_x_678_);
v___x_679_ = lean_box(0);
return v___x_679_;
}
else
{
lean_object* v_tail_680_; 
v_tail_680_ = lean_ctor_get(v_x_677_, 1);
if (lean_obj_tag(v_tail_680_) == 0)
{
lean_object* v_head_681_; lean_object* v___x_682_; 
lean_dec(v_x_678_);
v_head_681_ = lean_ctor_get(v_x_677_, 0);
lean_inc(v_head_681_);
lean_dec_ref(v_x_677_);
v___x_682_ = l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg(v_head_681_);
return v___x_682_;
}
else
{
lean_object* v_head_683_; lean_object* v___x_684_; lean_object* v___x_685_; 
lean_inc(v_tail_680_);
v_head_683_ = lean_ctor_get(v_x_677_, 0);
lean_inc(v_head_683_);
lean_dec_ref(v_x_677_);
v___x_684_ = l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg(v_head_683_);
v___x_685_ = l_List_foldl___at___00Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2_spec__4(v_x_678_, v___x_684_, v_tail_680_);
return v___x_685_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1___redArg(lean_object* v_a_686_){
_start:
{
if (lean_obj_tag(v_a_686_) == 0)
{
lean_object* v___x_687_; 
v___x_687_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__1));
return v___x_687_;
}
else
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; uint8_t v___x_696_; lean_object* v___x_697_; 
v___x_688_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__3));
v___x_689_ = l_Std_Format_joinSep___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__2(v_a_686_, v___x_688_);
v___x_690_ = lean_obj_once(&l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6, &l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6_once, _init_l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__6);
v___x_691_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__7));
v___x_692_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___x_689_);
v___x_693_ = ((lean_object*)(l_List_repr___at___00Lean_Level_Normalize_instReprNode_repr_spec__0___redArg___closed__8));
v___x_694_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_692_);
lean_ctor_set(v___x_694_, 1, v___x_693_);
v___x_695_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_690_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
v___x_696_ = 0;
v___x_697_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_697_, 0, v___x_695_);
lean_ctor_set_uint8(v___x_697_, sizeof(void*)*1, v___x_696_);
return v___x_697_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___lam__0(lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_700_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__6));
v___x_701_ = lean_box(0);
v___x_702_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Level_Normalize_instReprNormLevel_spec__0(v___x_701_, v___y_698_);
v___x_703_ = l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1___redArg(v___x_702_);
v___x_704_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_704_, 0, v___x_700_);
lean_ctor_set(v___x_704_, 1, v___x_703_);
v___x_705_ = l_Repr_addAppParen(v___x_704_, v___y_699_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instReprNormLevel___lam__0___boxed(lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_res_708_; 
v_res_708_ = l_Lean_Level_Normalize_instReprNormLevel___lam__0(v___y_706_, v___y_707_);
lean_dec(v___y_707_);
lean_dec(v___y_706_);
return v_res_708_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1(lean_object* v_a_711_, lean_object* v_n_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1___redArg(v_a_711_);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1___boxed(lean_object* v_a_714_, lean_object* v_n_715_){
_start:
{
lean_object* v_res_716_; 
v_res_716_ = l_List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1(v_a_714_, v_n_715_);
lean_dec(v_n_715_);
return v_res_716_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1(lean_object* v_x_717_, lean_object* v_x_718_){
_start:
{
lean_object* v___x_719_; 
v___x_719_ = l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___redArg(v_x_717_);
return v___x_719_;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1___boxed(lean_object* v_x_720_, lean_object* v_x_721_){
_start:
{
lean_object* v_res_722_; 
v_res_722_ = l_Prod_repr___at___00List_repr___at___00Lean_Level_Normalize_instReprNormLevel_spec__1_spec__1(v_x_720_, v_x_721_);
lean_dec(v_x_721_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__0(lean_object* v___x_723_, lean_object* v_l_u2081_724_, lean_object* v___x_725_, lean_object* v___x_726_, lean_object* v___x_727_, lean_object* v_a_728_, lean_object* v_b_729_, lean_object* v_acc_730_){
_start:
{
lean_object* v___x_731_; lean_object* v___x_732_; uint8_t v___x_733_; 
v___x_731_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_723_, v_l_u2081_724_, v_a_728_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_b_729_);
v___x_733_ = l_Option_instBEq_beq___redArg(v___x_725_, v___x_731_, v___x_732_);
if (v___x_733_ == 0)
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; 
lean_dec_ref(v___x_727_);
v___x_734_ = lean_box(v___x_733_);
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
v___x_736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
lean_ctor_set(v___x_736_, 1, v___x_726_);
v___x_737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_737_, 0, v___x_736_);
return v___x_737_;
}
else
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_738_, 0, v___x_727_);
return v___x_738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__0___boxed(lean_object* v___x_739_, lean_object* v_l_u2081_740_, lean_object* v___x_741_, lean_object* v___x_742_, lean_object* v___x_743_, lean_object* v_a_744_, lean_object* v_b_745_, lean_object* v_acc_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l_Lean_Level_Normalize_instBEqNormLevel___lam__0(v___x_739_, v_l_u2081_740_, v___x_741_, v___x_742_, v___x_743_, v_a_744_, v_b_745_, v_acc_746_);
lean_dec_ref(v_acc_746_);
return v_res_747_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__1(lean_object* v___x_748_, lean_object* v_l_u2082_749_, lean_object* v___x_750_, lean_object* v___x_751_, lean_object* v___x_752_, lean_object* v_a_753_, lean_object* v_b_754_, lean_object* v_acc_755_){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; uint8_t v___x_758_; 
v___x_756_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___redArg(v___x_748_, v_l_u2082_749_, v_a_753_);
v___x_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_757_, 0, v_b_754_);
v___x_758_ = l_Option_instBEq_beq___redArg(v___x_750_, v___x_756_, v___x_757_);
if (v___x_758_ == 0)
{
lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
lean_dec_ref(v___x_752_);
v___x_759_ = lean_box(v___x_758_);
v___x_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_760_, 0, v___x_759_);
v___x_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_760_);
lean_ctor_set(v___x_761_, 1, v___x_751_);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_763_, 0, v___x_752_);
return v___x_763_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__1___boxed(lean_object* v___x_764_, lean_object* v_l_u2082_765_, lean_object* v___x_766_, lean_object* v___x_767_, lean_object* v___x_768_, lean_object* v_a_769_, lean_object* v_b_770_, lean_object* v_acc_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_Level_Normalize_instBEqNormLevel___lam__1(v___x_764_, v_l_u2082_765_, v___x_766_, v___x_767_, v___x_768_, v_a_769_, v_b_770_, v_acc_771_);
lean_dec_ref(v_acc_771_);
return v_res_772_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_instBEqNormLevel___lam__2(lean_object* v___x_778_, lean_object* v_l_u2081_779_, lean_object* v_l_u2082_780_){
_start:
{
lean_object* v___y_782_; lean_object* v___y_796_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___f_805_; lean_object* v___x_806_; lean_object* v_a_807_; 
v___x_801_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__0));
v___x_802_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__16));
v___x_803_ = lean_box(0);
v___x_804_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
lean_inc_ref(v___x_778_);
lean_inc(v_l_u2082_780_);
v___f_805_ = lean_alloc_closure((void*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__1___boxed), 8, 5);
lean_closure_set(v___f_805_, 0, v___x_801_);
lean_closure_set(v___f_805_, 1, v_l_u2082_780_);
lean_closure_set(v___f_805_, 2, v___x_778_);
lean_closure_set(v___f_805_, 3, v___x_803_);
lean_closure_set(v___f_805_, 4, v___x_804_);
lean_inc(v_l_u2081_779_);
v___x_806_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_802_, v___f_805_, v___x_804_, v_l_u2081_779_);
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec(v___x_806_);
v___y_796_ = v_a_807_;
goto v___jp_795_;
v___jp_781_:
{
lean_object* v_fst_783_; 
v_fst_783_ = lean_ctor_get(v___y_782_, 0);
lean_inc(v_fst_783_);
lean_dec_ref(v___y_782_);
if (lean_obj_tag(v_fst_783_) == 0)
{
uint8_t v___x_784_; 
v___x_784_ = 1;
return v___x_784_;
}
else
{
lean_object* v_val_785_; uint8_t v___x_786_; 
v_val_785_ = lean_ctor_get(v_fst_783_, 0);
lean_inc(v_val_785_);
lean_dec_ref(v_fst_783_);
v___x_786_ = lean_unbox(v_val_785_);
lean_dec(v_val_785_);
return v___x_786_;
}
}
v___jp_787_:
{
lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___f_792_; lean_object* v___x_793_; lean_object* v_a_794_; 
v___x_788_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__0));
v___x_789_ = ((lean_object*)(l_Lean_Level_Normalize_instReprNormLevel___aux__1___closed__16));
v___x_790_ = lean_box(0);
v___x_791_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___f_792_ = lean_alloc_closure((void*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__0___boxed), 8, 5);
lean_closure_set(v___f_792_, 0, v___x_788_);
lean_closure_set(v___f_792_, 1, v_l_u2081_779_);
lean_closure_set(v___f_792_, 2, v___x_778_);
lean_closure_set(v___f_792_, 3, v___x_790_);
lean_closure_set(v___f_792_, 4, v___x_791_);
v___x_793_ = l_Std_DTreeMap_Internal_Impl_forInStep___redArg(v___x_789_, v___f_792_, v___x_791_, v_l_u2082_780_);
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec(v___x_793_);
v___y_782_ = v_a_794_;
goto v___jp_781_;
}
v___jp_795_:
{
lean_object* v_fst_797_; 
v_fst_797_ = lean_ctor_get(v___y_796_, 0);
lean_inc(v_fst_797_);
lean_dec_ref(v___y_796_);
if (lean_obj_tag(v_fst_797_) == 0)
{
goto v___jp_787_;
}
else
{
lean_object* v_val_798_; uint8_t v___x_799_; 
v_val_798_ = lean_ctor_get(v_fst_797_, 0);
lean_inc(v_val_798_);
lean_dec_ref(v_fst_797_);
v___x_799_ = lean_unbox(v_val_798_);
if (v___x_799_ == 0)
{
uint8_t v___x_800_; 
lean_dec(v_l_u2082_780_);
lean_dec(v_l_u2081_779_);
lean_dec_ref(v___x_778_);
v___x_800_ = lean_unbox(v_val_798_);
lean_dec(v_val_798_);
return v___x_800_;
}
else
{
lean_dec(v_val_798_);
goto v___jp_787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_instBEqNormLevel___lam__2___boxed(lean_object* v___x_808_, lean_object* v_l_u2081_809_, lean_object* v_l_u2082_810_){
_start:
{
uint8_t v_res_811_; lean_object* v_r_812_; 
v_res_811_ = l_Lean_Level_Normalize_instBEqNormLevel___lam__2(v___x_808_, v_l_u2081_809_, v_l_u2082_810_);
v_r_812_ = lean_box(v_res_811_);
return v_r_812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_VarNode_addVar(lean_object* v_v_816_, lean_object* v_k_817_, lean_object* v_x_818_){
_start:
{
if (lean_obj_tag(v_x_818_) == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_819_, 0, v_v_816_);
lean_ctor_set(v___x_819_, 1, v_k_817_);
v___x_820_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
lean_ctor_set(v___x_820_, 1, v_x_818_);
return v___x_820_;
}
else
{
lean_object* v_head_821_; lean_object* v_tail_822_; lean_object* v___y_824_; lean_object* v_var_827_; lean_object* v_offset_828_; uint8_t v___x_829_; 
v_head_821_ = lean_ctor_get(v_x_818_, 0);
lean_inc(v_head_821_);
v_tail_822_ = lean_ctor_get(v_x_818_, 1);
v_var_827_ = lean_ctor_get(v_head_821_, 0);
v_offset_828_ = lean_ctor_get(v_head_821_, 1);
v___x_829_ = l_Lean_Name_cmp(v_v_816_, v_var_827_);
switch(v___x_829_)
{
case 0:
{
lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_837_; 
v_isSharedCheck_837_ = !lean_is_exclusive(v_head_821_);
if (v_isSharedCheck_837_ == 0)
{
lean_object* v_unused_838_; lean_object* v_unused_839_; 
v_unused_838_ = lean_ctor_get(v_head_821_, 1);
lean_dec(v_unused_838_);
v_unused_839_ = lean_ctor_get(v_head_821_, 0);
lean_dec(v_unused_839_);
v___x_831_ = v_head_821_;
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
else
{
lean_dec(v_head_821_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_837_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
lean_ctor_set(v___x_831_, 1, v_k_817_);
lean_ctor_set(v___x_831_, 0, v_v_816_);
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v_v_816_);
lean_ctor_set(v_reuseFailAlloc_836_, 1, v_k_817_);
v___x_834_ = v_reuseFailAlloc_836_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
lean_object* v___x_835_; 
v___x_835_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_x_818_);
return v___x_835_;
}
}
}
case 1:
{
uint8_t v___x_840_; 
lean_inc(v_offset_828_);
lean_inc(v_tail_822_);
lean_dec_ref(v_x_818_);
lean_dec(v_head_821_);
v___x_840_ = lean_nat_dec_le(v_offset_828_, v_k_817_);
if (v___x_840_ == 0)
{
lean_dec(v_k_817_);
v___y_824_ = v_offset_828_;
goto v___jp_823_;
}
else
{
lean_dec(v_offset_828_);
v___y_824_ = v_k_817_;
goto v___jp_823_;
}
}
default: 
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
lean_inc(v_tail_822_);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_818_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; lean_object* v_unused_850_; 
v_unused_849_ = lean_ctor_get(v_x_818_, 1);
lean_dec(v_unused_849_);
v_unused_850_ = lean_ctor_get(v_x_818_, 0);
lean_dec(v_unused_850_);
v___x_842_ = v_x_818_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_x_818_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = l_Lean_Level_Normalize_VarNode_addVar(v_v_816_, v_k_817_, v_tail_822_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 1, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v_head_821_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
v___jp_823_:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v_v_816_);
lean_ctor_set(v___x_825_, 1, v___y_824_);
v___x_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_826_, 0, v___x_825_);
lean_ctor_set(v___x_826_, 1, v_tail_822_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT uint8_t l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(lean_object* v_x_851_, lean_object* v_x_852_){
_start:
{
if (lean_obj_tag(v_x_851_) == 0)
{
if (lean_obj_tag(v_x_852_) == 0)
{
uint8_t v___x_853_; 
v___x_853_ = 1;
return v___x_853_;
}
else
{
uint8_t v___x_854_; 
v___x_854_ = 0;
return v___x_854_;
}
}
else
{
if (lean_obj_tag(v_x_852_) == 0)
{
uint8_t v___x_855_; 
v___x_855_ = 2;
return v___x_855_;
}
else
{
lean_object* v_head_856_; lean_object* v_tail_857_; lean_object* v_head_858_; lean_object* v_tail_859_; uint8_t v___x_860_; 
v_head_856_ = lean_ctor_get(v_x_851_, 0);
v_tail_857_ = lean_ctor_get(v_x_851_, 1);
v_head_858_ = lean_ctor_get(v_x_852_, 0);
v_tail_859_ = lean_ctor_get(v_x_852_, 1);
v___x_860_ = l_Lean_Name_cmp(v_head_856_, v_head_858_);
if (v___x_860_ == 1)
{
v_x_851_ = v_tail_857_;
v_x_852_ = v_tail_859_;
goto _start;
}
else
{
return v___x_860_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0___boxed(lean_object* v_x_862_, lean_object* v_x_863_){
_start:
{
uint8_t v_res_864_; lean_object* v_r_865_; 
v_res_864_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_x_862_, v_x_863_);
lean_dec(v_x_863_);
lean_dec(v_x_862_);
v_r_865_ = lean_box(v_res_864_);
return v_r_865_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addVar_spec__1(lean_object* v_v_866_, lean_object* v_k_867_, lean_object* v_k_868_, lean_object* v_t_869_){
_start:
{
if (lean_obj_tag(v_t_869_) == 0)
{
lean_object* v_size_870_; lean_object* v_k_871_; lean_object* v_v_872_; lean_object* v_l_873_; lean_object* v_r_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_901_; 
v_size_870_ = lean_ctor_get(v_t_869_, 0);
v_k_871_ = lean_ctor_get(v_t_869_, 1);
v_v_872_ = lean_ctor_get(v_t_869_, 2);
v_l_873_ = lean_ctor_get(v_t_869_, 3);
v_r_874_ = lean_ctor_get(v_t_869_, 4);
v_isSharedCheck_901_ = !lean_is_exclusive(v_t_869_);
if (v_isSharedCheck_901_ == 0)
{
v___x_876_ = v_t_869_;
v_isShared_877_ = v_isSharedCheck_901_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_r_874_);
lean_inc(v_l_873_);
lean_inc(v_v_872_);
lean_inc(v_k_871_);
lean_inc(v_size_870_);
lean_dec(v_t_869_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_901_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
uint8_t v___x_878_; 
v___x_878_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_868_, v_k_871_);
switch(v___x_878_)
{
case 0:
{
lean_object* v___x_879_; lean_object* v___x_881_; 
v___x_879_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addVar_spec__1(v_v_866_, v_k_867_, v_k_868_, v_l_873_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 3, v___x_879_);
v___x_881_ = v___x_876_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_size_870_);
lean_ctor_set(v_reuseFailAlloc_882_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_882_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_882_, 3, v___x_879_);
lean_ctor_set(v_reuseFailAlloc_882_, 4, v_r_874_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
case 1:
{
lean_object* v_path_883_; lean_object* v_const_884_; lean_object* v_var_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_896_; 
lean_dec(v_k_871_);
v_path_883_ = lean_ctor_get(v_v_872_, 0);
v_const_884_ = lean_ctor_get(v_v_872_, 1);
v_var_885_ = lean_ctor_get(v_v_872_, 2);
v_isSharedCheck_896_ = !lean_is_exclusive(v_v_872_);
if (v_isSharedCheck_896_ == 0)
{
v___x_887_ = v_v_872_;
v_isShared_888_ = v_isSharedCheck_896_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_var_885_);
lean_inc(v_const_884_);
lean_inc(v_path_883_);
lean_dec(v_v_872_);
v___x_887_ = lean_box(0);
v_isShared_888_ = v_isSharedCheck_896_;
goto v_resetjp_886_;
}
v_resetjp_886_:
{
lean_object* v___x_889_; lean_object* v___x_891_; 
v___x_889_ = l_Lean_Level_Normalize_VarNode_addVar(v_v_866_, v_k_867_, v_var_885_);
if (v_isShared_888_ == 0)
{
lean_ctor_set(v___x_887_, 2, v___x_889_);
v___x_891_ = v___x_887_;
goto v_reusejp_890_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_path_883_);
lean_ctor_set(v_reuseFailAlloc_895_, 1, v_const_884_);
lean_ctor_set(v_reuseFailAlloc_895_, 2, v___x_889_);
v___x_891_ = v_reuseFailAlloc_895_;
goto v_reusejp_890_;
}
v_reusejp_890_:
{
lean_object* v___x_893_; 
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 2, v___x_891_);
lean_ctor_set(v___x_876_, 1, v_k_868_);
v___x_893_ = v___x_876_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_size_870_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_k_868_);
lean_ctor_set(v_reuseFailAlloc_894_, 2, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_894_, 3, v_l_873_);
lean_ctor_set(v_reuseFailAlloc_894_, 4, v_r_874_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
default: 
{
lean_object* v___x_897_; lean_object* v___x_899_; 
v___x_897_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addVar_spec__1(v_v_866_, v_k_867_, v_k_868_, v_r_874_);
if (v_isShared_877_ == 0)
{
lean_ctor_set(v___x_876_, 4, v___x_897_);
v___x_899_ = v___x_876_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_size_870_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_k_871_);
lean_ctor_set(v_reuseFailAlloc_900_, 2, v_v_872_);
lean_ctor_set(v_reuseFailAlloc_900_, 3, v_l_873_);
lean_ctor_set(v_reuseFailAlloc_900_, 4, v___x_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
else
{
lean_dec(v_k_868_);
lean_dec(v_k_867_);
lean_dec(v_v_866_);
return v_t_869_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_addVar(lean_object* v_v_902_, lean_object* v_k_903_, lean_object* v_path_x27_904_, lean_object* v_s_905_){
_start:
{
lean_object* v___x_906_; 
v___x_906_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addVar_spec__1(v_v_902_, v_k_903_, v_path_x27_904_, v_s_905_);
return v___x_906_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg___lam__0(lean_object* v_v_907_, lean_object* v_k_908_, lean_object* v_x_909_){
_start:
{
if (lean_obj_tag(v_x_909_) == 0)
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_910_ = lean_box(0);
v___x_911_ = lean_unsigned_to_nat(0u);
v___x_912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_912_, 0, v_v_907_);
lean_ctor_set(v___x_912_, 1, v_k_908_);
v___x_913_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_913_, 0, v___x_912_);
lean_ctor_set(v___x_913_, 1, v___x_910_);
v___x_914_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_914_, 0, v___x_910_);
lean_ctor_set(v___x_914_, 1, v___x_911_);
lean_ctor_set(v___x_914_, 2, v___x_913_);
v___x_915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_914_);
return v___x_915_;
}
else
{
lean_object* v_val_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_934_; 
v_val_916_ = lean_ctor_get(v_x_909_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v_x_909_);
if (v_isSharedCheck_934_ == 0)
{
v___x_918_ = v_x_909_;
v_isShared_919_ = v_isSharedCheck_934_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_val_916_);
lean_dec(v_x_909_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_934_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v_path_920_; lean_object* v_const_921_; lean_object* v_var_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_933_; 
v_path_920_ = lean_ctor_get(v_val_916_, 0);
v_const_921_ = lean_ctor_get(v_val_916_, 1);
v_var_922_ = lean_ctor_get(v_val_916_, 2);
v_isSharedCheck_933_ = !lean_is_exclusive(v_val_916_);
if (v_isSharedCheck_933_ == 0)
{
v___x_924_ = v_val_916_;
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_var_922_);
lean_inc(v_const_921_);
lean_inc(v_path_920_);
lean_dec(v_val_916_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_933_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_926_; lean_object* v___x_928_; 
v___x_926_ = l_Lean_Level_Normalize_VarNode_addVar(v_v_907_, v_k_908_, v_var_922_);
if (v_isShared_925_ == 0)
{
lean_ctor_set(v___x_924_, 2, v___x_926_);
v___x_928_ = v___x_924_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_path_920_);
lean_ctor_set(v_reuseFailAlloc_932_, 1, v_const_921_);
lean_ctor_set(v_reuseFailAlloc_932_, 2, v___x_926_);
v___x_928_ = v_reuseFailAlloc_932_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
lean_object* v___x_930_; 
if (v_isShared_919_ == 0)
{
lean_ctor_set(v___x_918_, 0, v___x_928_);
v___x_930_ = v___x_918_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(lean_object* v_v_935_, lean_object* v_k_936_, lean_object* v_k_937_, lean_object* v_t_938_){
_start:
{
if (lean_obj_tag(v_t_938_) == 0)
{
lean_object* v_size_939_; lean_object* v_k_940_; lean_object* v_v_941_; lean_object* v_l_942_; lean_object* v_r_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_958_; 
v_size_939_ = lean_ctor_get(v_t_938_, 0);
v_k_940_ = lean_ctor_get(v_t_938_, 1);
v_v_941_ = lean_ctor_get(v_t_938_, 2);
v_l_942_ = lean_ctor_get(v_t_938_, 3);
v_r_943_ = lean_ctor_get(v_t_938_, 4);
v_isSharedCheck_958_ = !lean_is_exclusive(v_t_938_);
if (v_isSharedCheck_958_ == 0)
{
v___x_945_ = v_t_938_;
v_isShared_946_ = v_isSharedCheck_958_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_r_943_);
lean_inc(v_l_942_);
lean_inc(v_v_941_);
lean_inc(v_k_940_);
lean_inc(v_size_939_);
lean_dec(v_t_938_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_958_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
uint8_t v___x_947_; 
v___x_947_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_937_, v_k_940_);
switch(v___x_947_)
{
case 0:
{
lean_object* v_impl_948_; lean_object* v___x_949_; 
lean_del_object(v___x_945_);
lean_dec(v_size_939_);
v_impl_948_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(v_v_935_, v_k_936_, v_k_937_, v_l_942_);
v___x_949_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_940_, v_v_941_, v_impl_948_, v_r_943_);
return v___x_949_;
}
case 1:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v_val_952_; lean_object* v___x_954_; 
lean_dec(v_k_940_);
v___x_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_950_, 0, v_v_941_);
v___x_951_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg___lam__0(v_v_935_, v_k_936_, v___x_950_);
v_val_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_val_952_);
lean_dec(v___x_951_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 2, v_val_952_);
lean_ctor_set(v___x_945_, 1, v_k_937_);
v___x_954_ = v___x_945_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_size_939_);
lean_ctor_set(v_reuseFailAlloc_955_, 1, v_k_937_);
lean_ctor_set(v_reuseFailAlloc_955_, 2, v_val_952_);
lean_ctor_set(v_reuseFailAlloc_955_, 3, v_l_942_);
lean_ctor_set(v_reuseFailAlloc_955_, 4, v_r_943_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
default: 
{
lean_object* v_impl_956_; lean_object* v___x_957_; 
lean_del_object(v___x_945_);
lean_dec(v_size_939_);
v_impl_956_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(v_v_935_, v_k_936_, v_k_937_, v_r_943_);
v___x_957_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(v_k_940_, v_v_941_, v_l_942_, v_impl_956_);
return v___x_957_;
}
}
}
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v_val_961_; lean_object* v___x_962_; lean_object* v___x_963_; 
v___x_959_ = lean_box(0);
v___x_960_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg___lam__0(v_v_935_, v_k_936_, v___x_959_);
v_val_961_ = lean_ctor_get(v___x_960_, 0);
lean_inc(v_val_961_);
lean_dec(v___x_960_);
v___x_962_ = lean_unsigned_to_nat(1u);
v___x_963_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_963_, 0, v___x_962_);
lean_ctor_set(v___x_963_, 1, v_k_937_);
lean_ctor_set(v___x_963_, 2, v_val_961_);
lean_ctor_set(v___x_963_, 3, v_t_938_);
lean_ctor_set(v___x_963_, 4, v_t_938_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_addNode(lean_object* v_v_964_, lean_object* v_k_965_, lean_object* v_path_x27_966_, lean_object* v_s_967_){
_start:
{
lean_object* v___x_968_; 
v___x_968_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(v_v_964_, v_k_965_, v_path_x27_966_, v_s_967_);
return v___x_968_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0(lean_object* v_v_969_, lean_object* v_k_970_, lean_object* v_k_971_, lean_object* v_t_972_, lean_object* v_hl_973_){
_start:
{
lean_object* v___x_974_; 
v___x_974_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(v_v_969_, v_k_970_, v_k_971_, v_t_972_);
return v___x_974_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addConst_spec__0(lean_object* v_k_975_, lean_object* v_k_976_, lean_object* v_t_977_){
_start:
{
if (lean_obj_tag(v_t_977_) == 0)
{
lean_object* v_size_978_; lean_object* v_k_979_; lean_object* v_v_980_; lean_object* v_l_981_; lean_object* v_r_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_1011_; 
v_size_978_ = lean_ctor_get(v_t_977_, 0);
v_k_979_ = lean_ctor_get(v_t_977_, 1);
v_v_980_ = lean_ctor_get(v_t_977_, 2);
v_l_981_ = lean_ctor_get(v_t_977_, 3);
v_r_982_ = lean_ctor_get(v_t_977_, 4);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_t_977_);
if (v_isSharedCheck_1011_ == 0)
{
v___x_984_ = v_t_977_;
v_isShared_985_ = v_isSharedCheck_1011_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_r_982_);
lean_inc(v_l_981_);
lean_inc(v_v_980_);
lean_inc(v_k_979_);
lean_inc(v_size_978_);
lean_dec(v_t_977_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_1011_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
uint8_t v___x_986_; 
v___x_986_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_976_, v_k_979_);
switch(v___x_986_)
{
case 0:
{
lean_object* v___x_987_; lean_object* v___x_989_; 
v___x_987_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addConst_spec__0(v_k_975_, v_k_976_, v_l_981_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 3, v___x_987_);
v___x_989_ = v___x_984_;
goto v_reusejp_988_;
}
else
{
lean_object* v_reuseFailAlloc_990_; 
v_reuseFailAlloc_990_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_990_, 0, v_size_978_);
lean_ctor_set(v_reuseFailAlloc_990_, 1, v_k_979_);
lean_ctor_set(v_reuseFailAlloc_990_, 2, v_v_980_);
lean_ctor_set(v_reuseFailAlloc_990_, 3, v___x_987_);
lean_ctor_set(v_reuseFailAlloc_990_, 4, v_r_982_);
v___x_989_ = v_reuseFailAlloc_990_;
goto v_reusejp_988_;
}
v_reusejp_988_:
{
return v___x_989_;
}
}
case 1:
{
lean_object* v_path_991_; lean_object* v_const_992_; lean_object* v_var_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1006_; 
lean_dec(v_k_979_);
v_path_991_ = lean_ctor_get(v_v_980_, 0);
v_const_992_ = lean_ctor_get(v_v_980_, 1);
v_var_993_ = lean_ctor_get(v_v_980_, 2);
v_isSharedCheck_1006_ = !lean_is_exclusive(v_v_980_);
if (v_isSharedCheck_1006_ == 0)
{
v___x_995_ = v_v_980_;
v_isShared_996_ = v_isSharedCheck_1006_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_var_993_);
lean_inc(v_const_992_);
lean_inc(v_path_991_);
lean_dec(v_v_980_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1006_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___y_998_; uint8_t v___x_1005_; 
v___x_1005_ = lean_nat_dec_le(v_k_975_, v_const_992_);
if (v___x_1005_ == 0)
{
lean_dec(v_const_992_);
v___y_998_ = v_k_975_;
goto v___jp_997_;
}
else
{
lean_dec(v_k_975_);
v___y_998_ = v_const_992_;
goto v___jp_997_;
}
v___jp_997_:
{
lean_object* v___x_1000_; 
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v___y_998_);
v___x_1000_ = v___x_995_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_path_991_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v___y_998_);
lean_ctor_set(v_reuseFailAlloc_1004_, 2, v_var_993_);
v___x_1000_ = v_reuseFailAlloc_1004_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
lean_object* v___x_1002_; 
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 2, v___x_1000_);
lean_ctor_set(v___x_984_, 1, v_k_976_);
v___x_1002_ = v___x_984_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v_size_978_);
lean_ctor_set(v_reuseFailAlloc_1003_, 1, v_k_976_);
lean_ctor_set(v_reuseFailAlloc_1003_, 2, v___x_1000_);
lean_ctor_set(v_reuseFailAlloc_1003_, 3, v_l_981_);
lean_ctor_set(v_reuseFailAlloc_1003_, 4, v_r_982_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
}
}
}
default: 
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
v___x_1007_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addConst_spec__0(v_k_975_, v_k_976_, v_r_982_);
if (v_isShared_985_ == 0)
{
lean_ctor_set(v___x_984_, 4, v___x_1007_);
v___x_1009_ = v___x_984_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v_size_978_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_k_979_);
lean_ctor_set(v_reuseFailAlloc_1010_, 2, v_v_980_);
lean_ctor_set(v_reuseFailAlloc_1010_, 3, v_l_981_);
lean_ctor_set(v_reuseFailAlloc_1010_, 4, v___x_1007_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
else
{
lean_dec(v_k_976_);
lean_dec(v_k_975_);
return v_t_977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_addConst(lean_object* v_k_1012_, lean_object* v_path_1013_, lean_object* v_acc_1014_){
_start:
{
uint8_t v___y_1016_; lean_object* v___x_1018_; uint8_t v___x_1019_; 
v___x_1018_ = lean_unsigned_to_nat(0u);
v___x_1019_ = lean_nat_dec_eq(v_k_1012_, v___x_1018_);
if (v___x_1019_ == 0)
{
lean_object* v___x_1020_; uint8_t v___x_1021_; 
v___x_1020_ = lean_unsigned_to_nat(1u);
v___x_1021_ = lean_nat_dec_eq(v_k_1012_, v___x_1020_);
if (v___x_1021_ == 0)
{
v___y_1016_ = v___x_1021_;
goto v___jp_1015_;
}
else
{
uint8_t v___x_1022_; 
v___x_1022_ = l_List_isEmpty___redArg(v_path_1013_);
if (v___x_1022_ == 0)
{
v___y_1016_ = v___x_1021_;
goto v___jp_1015_;
}
else
{
v___y_1016_ = v___x_1019_;
goto v___jp_1015_;
}
}
}
else
{
v___y_1016_ = v___x_1019_;
goto v___jp_1015_;
}
v___jp_1015_:
{
if (v___y_1016_ == 0)
{
lean_object* v___x_1017_; 
v___x_1017_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addConst_spec__0(v_k_1012_, v_path_1013_, v_acc_1014_);
return v___x_1017_;
}
else
{
lean_dec(v_path_1013_);
lean_dec(v_k_1012_);
return v_acc_1014_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_normalizeAux(lean_object* v_l_1023_, lean_object* v_path_1024_, lean_object* v_k_1025_, lean_object* v_acc_1026_){
_start:
{
switch(lean_obj_tag(v_l_1023_))
{
case 0:
{
lean_object* v___x_1027_; 
v___x_1027_ = l_Lean_Level_Normalize_NormLevel_addConst(v_k_1025_, v_path_1024_, v_acc_1026_);
return v___x_1027_;
}
case 1:
{
lean_object* v_a_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; 
v_a_1028_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_a_1028_);
lean_dec_ref(v_l_1023_);
v___x_1029_ = lean_unsigned_to_nat(1u);
v___x_1030_ = lean_nat_add(v_k_1025_, v___x_1029_);
lean_dec(v_k_1025_);
v_l_1023_ = v_a_1028_;
v_k_1025_ = v___x_1030_;
goto _start;
}
case 2:
{
lean_object* v_a_1032_; lean_object* v_a_1033_; lean_object* v___x_1034_; 
v_a_1032_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_a_1032_);
v_a_1033_ = lean_ctor_get(v_l_1023_, 1);
lean_inc(v_a_1033_);
lean_dec_ref(v_l_1023_);
lean_inc(v_k_1025_);
lean_inc(v_path_1024_);
v___x_1034_ = l_Lean_Level_Normalize_normalizeAux(v_a_1032_, v_path_1024_, v_k_1025_, v_acc_1026_);
v_l_1023_ = v_a_1033_;
v_acc_1026_ = v___x_1034_;
goto _start;
}
case 3:
{
lean_object* v_a_1036_; 
v_a_1036_ = lean_ctor_get(v_l_1023_, 1);
lean_inc(v_a_1036_);
switch(lean_obj_tag(v_a_1036_))
{
case 0:
{
lean_object* v___x_1037_; 
lean_dec_ref(v_l_1023_);
v___x_1037_ = l_Lean_Level_Normalize_NormLevel_addConst(v_k_1025_, v_path_1024_, v_acc_1026_);
return v___x_1037_;
}
case 1:
{
lean_object* v_a_1038_; lean_object* v_a_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; 
v_a_1038_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_a_1038_);
lean_dec_ref(v_l_1023_);
v_a_1039_ = lean_ctor_get(v_a_1036_, 0);
lean_inc(v_a_1039_);
lean_dec_ref(v_a_1036_);
v___x_1040_ = lean_unsigned_to_nat(1u);
v___x_1041_ = lean_nat_add(v_k_1025_, v___x_1040_);
lean_inc(v_path_1024_);
v___x_1042_ = l_Lean_Level_Normalize_normalizeAux(v_a_1038_, v_path_1024_, v_k_1025_, v_acc_1026_);
v_l_1023_ = v_a_1039_;
v_k_1025_ = v___x_1041_;
v_acc_1026_ = v___x_1042_;
goto _start;
}
case 2:
{
lean_object* v_a_1044_; lean_object* v_a_1045_; lean_object* v_a_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; 
v_a_1044_ = lean_ctor_get(v_l_1023_, 0);
lean_inc_n(v_a_1044_, 2);
lean_dec_ref(v_l_1023_);
v_a_1045_ = lean_ctor_get(v_a_1036_, 0);
lean_inc(v_a_1045_);
v_a_1046_ = lean_ctor_get(v_a_1036_, 1);
lean_inc(v_a_1046_);
lean_dec_ref(v_a_1036_);
v___x_1047_ = l_Lean_Level_imax___override(v_a_1044_, v_a_1046_);
v___x_1048_ = l_Lean_Level_imax___override(v_a_1044_, v_a_1045_);
lean_inc(v_k_1025_);
lean_inc(v_path_1024_);
v___x_1049_ = l_Lean_Level_Normalize_normalizeAux(v___x_1048_, v_path_1024_, v_k_1025_, v_acc_1026_);
v_l_1023_ = v___x_1047_;
v_acc_1026_ = v___x_1049_;
goto _start;
}
case 3:
{
lean_object* v_a_1051_; lean_object* v_a_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_a_1051_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_a_1051_);
lean_dec_ref(v_l_1023_);
v_a_1052_ = lean_ctor_get(v_a_1036_, 1);
lean_inc(v_a_1052_);
v___x_1053_ = l_Lean_Level_imax___override(v_a_1051_, v_a_1052_);
lean_inc(v_k_1025_);
lean_inc(v_path_1024_);
v___x_1054_ = l_Lean_Level_Normalize_normalizeAux(v___x_1053_, v_path_1024_, v_k_1025_, v_acc_1026_);
v_l_1023_ = v_a_1036_;
v_acc_1026_ = v___x_1054_;
goto _start;
}
case 4:
{
lean_object* v_a_1056_; lean_object* v_a_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_a_1056_ = lean_ctor_get(v_l_1023_, 0);
lean_inc(v_a_1056_);
lean_dec_ref(v_l_1023_);
v_a_1057_ = lean_ctor_get(v_a_1036_, 0);
lean_inc_n(v_a_1057_, 2);
lean_dec_ref(v_a_1036_);
v___x_1058_ = ((lean_object*)(l_Lean_Level_Normalize_instOrdName___closed__0));
lean_inc(v_path_1024_);
v___x_1059_ = l_Lean_Level_Normalize_orderedInsert___redArg(v___x_1058_, v_a_1057_, v_path_1024_);
if (lean_obj_tag(v___x_1059_) == 0)
{
lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1060_ = lean_unsigned_to_nat(0u);
v___x_1061_ = lean_nat_dec_eq(v_k_1025_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_object* v___x_1062_; 
lean_inc(v_path_1024_);
lean_inc(v_k_1025_);
v___x_1062_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addVar_spec__1(v_a_1057_, v_k_1025_, v_path_1024_, v_acc_1026_);
v_l_1023_ = v_a_1056_;
v_acc_1026_ = v___x_1062_;
goto _start;
}
else
{
lean_dec(v_a_1057_);
v_l_1023_ = v_a_1056_;
goto _start;
}
}
else
{
lean_object* v_val_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; 
v_val_1065_ = lean_ctor_get(v___x_1059_, 0);
lean_inc_n(v_val_1065_, 2);
lean_dec_ref(v___x_1059_);
lean_inc_n(v_k_1025_, 2);
v___x_1066_ = l_Lean_Level_Normalize_NormLevel_addConst(v_k_1025_, v_path_1024_, v_acc_1026_);
v___x_1067_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(v_a_1057_, v_k_1025_, v_val_1065_, v___x_1066_);
v_l_1023_ = v_a_1056_;
v_path_1024_ = v_val_1065_;
v_acc_1026_ = v___x_1067_;
goto _start;
}
}
default: 
{
lean_dec_ref(v_a_1036_);
lean_dec_ref(v_l_1023_);
lean_dec(v_k_1025_);
lean_dec(v_path_1024_);
return v_acc_1026_;
}
}
}
case 4:
{
lean_object* v_a_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; 
v_a_1069_ = lean_ctor_get(v_l_1023_, 0);
lean_inc_n(v_a_1069_, 2);
lean_dec_ref(v_l_1023_);
v___x_1070_ = ((lean_object*)(l_Lean_Level_Normalize_instOrdName___closed__0));
lean_inc(v_path_1024_);
v___x_1071_ = l_Lean_Level_Normalize_orderedInsert___redArg(v___x_1070_, v_a_1069_, v_path_1024_);
if (lean_obj_tag(v___x_1071_) == 0)
{
lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1072_ = lean_unsigned_to_nat(0u);
v___x_1073_ = lean_nat_dec_eq(v_k_1025_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
v___x_1074_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_addVar_spec__1(v_a_1069_, v_k_1025_, v_path_1024_, v_acc_1026_);
return v___x_1074_;
}
else
{
lean_dec(v_a_1069_);
lean_dec(v_k_1025_);
lean_dec(v_path_1024_);
return v_acc_1026_;
}
}
else
{
lean_object* v_val_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_val_1075_ = lean_ctor_get(v___x_1071_, 0);
lean_inc(v_val_1075_);
lean_dec_ref(v___x_1071_);
lean_inc(v_k_1025_);
v___x_1076_ = l_Lean_Level_Normalize_NormLevel_addConst(v_k_1025_, v_path_1024_, v_acc_1026_);
v___x_1077_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_Level_Normalize_NormLevel_addNode_spec__0___redArg(v_a_1069_, v_k_1025_, v_val_1075_, v___x_1076_);
return v___x_1077_;
}
}
default: 
{
lean_dec_ref(v_l_1023_);
lean_dec(v_k_1025_);
lean_dec(v_path_1024_);
return v_acc_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__3_splitter___redArg(lean_object* v_l_1078_, lean_object* v_h__1_1079_, lean_object* v_h__2_1080_, lean_object* v_h__3_1081_, lean_object* v_h__4_1082_, lean_object* v_h__5_1083_, lean_object* v_h__6_1084_, lean_object* v_h__7_1085_, lean_object* v_h__8_1086_, lean_object* v_h__9_1087_, lean_object* v_h__10_1088_, lean_object* v_h__11_1089_){
_start:
{
switch(lean_obj_tag(v_l_1078_))
{
case 0:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v_h__11_1089_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__9_1087_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__4_1082_);
lean_dec(v_h__3_1081_);
lean_dec(v_h__2_1080_);
v___x_1090_ = lean_box(0);
v___x_1091_ = lean_apply_1(v_h__1_1079_, v___x_1090_);
return v___x_1091_;
}
case 1:
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
lean_dec(v_h__11_1089_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__9_1087_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__4_1082_);
lean_dec(v_h__2_1080_);
lean_dec(v_h__1_1079_);
v_a_1092_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1092_);
lean_dec_ref(v_l_1078_);
v___x_1093_ = lean_apply_1(v_h__3_1081_, v_a_1092_);
return v___x_1093_;
}
case 2:
{
lean_object* v_a_1094_; lean_object* v_a_1095_; lean_object* v___x_1096_; 
lean_dec(v_h__11_1089_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__9_1087_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__3_1081_);
lean_dec(v_h__2_1080_);
lean_dec(v_h__1_1079_);
v_a_1094_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1094_);
v_a_1095_ = lean_ctor_get(v_l_1078_, 1);
lean_inc(v_a_1095_);
lean_dec_ref(v_l_1078_);
v___x_1096_ = lean_apply_2(v_h__4_1082_, v_a_1094_, v_a_1095_);
return v___x_1096_;
}
case 3:
{
lean_object* v_a_1097_; 
lean_dec(v_h__11_1089_);
lean_dec(v_h__9_1087_);
lean_dec(v_h__4_1082_);
lean_dec(v_h__3_1081_);
lean_dec(v_h__1_1079_);
v_a_1097_ = lean_ctor_get(v_l_1078_, 1);
switch(lean_obj_tag(v_a_1097_))
{
case 0:
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
lean_dec(v_h__10_1088_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
v_a_1098_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v_l_1078_);
v___x_1099_ = lean_apply_1(v_h__2_1080_, v_a_1098_);
return v___x_1099_;
}
case 1:
{
lean_object* v_a_1100_; lean_object* v_a_1101_; lean_object* v___x_1102_; 
lean_inc_ref(v_a_1097_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__2_1080_);
v_a_1100_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1100_);
lean_dec_ref(v_l_1078_);
v_a_1101_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1101_);
lean_dec_ref(v_a_1097_);
v___x_1102_ = lean_apply_2(v_h__5_1083_, v_a_1100_, v_a_1101_);
return v___x_1102_;
}
case 2:
{
lean_object* v_a_1103_; lean_object* v_a_1104_; lean_object* v_a_1105_; lean_object* v___x_1106_; 
lean_inc_ref(v_a_1097_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__2_1080_);
v_a_1103_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1103_);
lean_dec_ref(v_l_1078_);
v_a_1104_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1104_);
v_a_1105_ = lean_ctor_get(v_a_1097_, 1);
lean_inc(v_a_1105_);
lean_dec_ref(v_a_1097_);
v___x_1106_ = lean_apply_3(v_h__6_1084_, v_a_1103_, v_a_1104_, v_a_1105_);
return v___x_1106_;
}
case 3:
{
lean_object* v_a_1107_; lean_object* v_a_1108_; lean_object* v_a_1109_; lean_object* v___x_1110_; 
lean_inc_ref(v_a_1097_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__2_1080_);
v_a_1107_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1107_);
lean_dec_ref(v_l_1078_);
v_a_1108_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1108_);
v_a_1109_ = lean_ctor_get(v_a_1097_, 1);
lean_inc(v_a_1109_);
lean_dec_ref(v_a_1097_);
v___x_1110_ = lean_apply_3(v_h__7_1085_, v_a_1107_, v_a_1108_, v_a_1109_);
return v___x_1110_;
}
case 4:
{
lean_object* v_a_1111_; lean_object* v_a_1112_; lean_object* v___x_1113_; 
lean_inc_ref(v_a_1097_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__2_1080_);
v_a_1111_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1111_);
lean_dec_ref(v_l_1078_);
v_a_1112_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1112_);
lean_dec_ref(v_a_1097_);
v___x_1113_ = lean_apply_2(v_h__8_1086_, v_a_1111_, v_a_1112_);
return v___x_1113_;
}
default: 
{
lean_object* v_a_1114_; lean_object* v_a_1115_; lean_object* v___x_1116_; 
lean_inc_ref(v_a_1097_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__2_1080_);
v_a_1114_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1114_);
lean_dec_ref(v_l_1078_);
v_a_1115_ = lean_ctor_get(v_a_1097_, 0);
lean_inc(v_a_1115_);
lean_dec_ref(v_a_1097_);
v___x_1116_ = lean_apply_2(v_h__10_1088_, v_a_1114_, v_a_1115_);
return v___x_1116_;
}
}
}
case 4:
{
lean_object* v_a_1117_; lean_object* v___x_1118_; 
lean_dec(v_h__10_1088_);
lean_dec(v_h__9_1087_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__4_1082_);
lean_dec(v_h__3_1081_);
lean_dec(v_h__2_1080_);
lean_dec(v_h__1_1079_);
v_a_1117_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1117_);
lean_dec_ref(v_l_1078_);
v___x_1118_ = lean_apply_1(v_h__11_1089_, v_a_1117_);
return v___x_1118_;
}
default: 
{
lean_object* v_a_1119_; lean_object* v___x_1120_; 
lean_dec(v_h__11_1089_);
lean_dec(v_h__10_1088_);
lean_dec(v_h__8_1086_);
lean_dec(v_h__7_1085_);
lean_dec(v_h__6_1084_);
lean_dec(v_h__5_1083_);
lean_dec(v_h__4_1082_);
lean_dec(v_h__3_1081_);
lean_dec(v_h__2_1080_);
lean_dec(v_h__1_1079_);
v_a_1119_ = lean_ctor_get(v_l_1078_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v_l_1078_);
v___x_1120_ = lean_apply_1(v_h__9_1087_, v_a_1119_);
return v___x_1120_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__3_splitter(lean_object* v_motive_1121_, lean_object* v_l_1122_, lean_object* v_h__1_1123_, lean_object* v_h__2_1124_, lean_object* v_h__3_1125_, lean_object* v_h__4_1126_, lean_object* v_h__5_1127_, lean_object* v_h__6_1128_, lean_object* v_h__7_1129_, lean_object* v_h__8_1130_, lean_object* v_h__9_1131_, lean_object* v_h__10_1132_, lean_object* v_h__11_1133_){
_start:
{
switch(lean_obj_tag(v_l_1122_))
{
case 0:
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
v___x_1134_ = lean_box(0);
v___x_1135_ = lean_apply_1(v_h__1_1123_, v___x_1134_);
return v___x_1135_;
}
case 1:
{
lean_object* v_a_1136_; lean_object* v___x_1137_; 
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_a_1136_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1136_);
lean_dec_ref(v_l_1122_);
v___x_1137_ = lean_apply_1(v_h__3_1125_, v_a_1136_);
return v___x_1137_;
}
case 2:
{
lean_object* v_a_1138_; lean_object* v_a_1139_; lean_object* v___x_1140_; 
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_a_1138_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1138_);
v_a_1139_ = lean_ctor_get(v_l_1122_, 1);
lean_inc(v_a_1139_);
lean_dec_ref(v_l_1122_);
v___x_1140_ = lean_apply_2(v_h__4_1126_, v_a_1138_, v_a_1139_);
return v___x_1140_;
}
case 3:
{
lean_object* v_a_1141_; 
lean_dec(v_h__11_1133_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__1_1123_);
v_a_1141_ = lean_ctor_get(v_l_1122_, 1);
switch(lean_obj_tag(v_a_1141_))
{
case 0:
{
lean_object* v_a_1142_; lean_object* v___x_1143_; 
lean_dec(v_h__10_1132_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
v_a_1142_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1142_);
lean_dec_ref(v_l_1122_);
v___x_1143_ = lean_apply_1(v_h__2_1124_, v_a_1142_);
return v___x_1143_;
}
case 1:
{
lean_object* v_a_1144_; lean_object* v_a_1145_; lean_object* v___x_1146_; 
lean_inc_ref(v_a_1141_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__2_1124_);
v_a_1144_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1144_);
lean_dec_ref(v_l_1122_);
v_a_1145_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_a_1145_);
lean_dec_ref(v_a_1141_);
v___x_1146_ = lean_apply_2(v_h__5_1127_, v_a_1144_, v_a_1145_);
return v___x_1146_;
}
case 2:
{
lean_object* v_a_1147_; lean_object* v_a_1148_; lean_object* v_a_1149_; lean_object* v___x_1150_; 
lean_inc_ref(v_a_1141_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__2_1124_);
v_a_1147_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v_l_1122_);
v_a_1148_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_a_1148_);
v_a_1149_ = lean_ctor_get(v_a_1141_, 1);
lean_inc(v_a_1149_);
lean_dec_ref(v_a_1141_);
v___x_1150_ = lean_apply_3(v_h__6_1128_, v_a_1147_, v_a_1148_, v_a_1149_);
return v___x_1150_;
}
case 3:
{
lean_object* v_a_1151_; lean_object* v_a_1152_; lean_object* v_a_1153_; lean_object* v___x_1154_; 
lean_inc_ref(v_a_1141_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__2_1124_);
v_a_1151_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1151_);
lean_dec_ref(v_l_1122_);
v_a_1152_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_a_1152_);
v_a_1153_ = lean_ctor_get(v_a_1141_, 1);
lean_inc(v_a_1153_);
lean_dec_ref(v_a_1141_);
v___x_1154_ = lean_apply_3(v_h__7_1129_, v_a_1151_, v_a_1152_, v_a_1153_);
return v___x_1154_;
}
case 4:
{
lean_object* v_a_1155_; lean_object* v_a_1156_; lean_object* v___x_1157_; 
lean_inc_ref(v_a_1141_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__2_1124_);
v_a_1155_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1155_);
lean_dec_ref(v_l_1122_);
v_a_1156_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_a_1156_);
lean_dec_ref(v_a_1141_);
v___x_1157_ = lean_apply_2(v_h__8_1130_, v_a_1155_, v_a_1156_);
return v___x_1157_;
}
default: 
{
lean_object* v_a_1158_; lean_object* v_a_1159_; lean_object* v___x_1160_; 
lean_inc_ref(v_a_1141_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__2_1124_);
v_a_1158_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1158_);
lean_dec_ref(v_l_1122_);
v_a_1159_ = lean_ctor_get(v_a_1141_, 0);
lean_inc(v_a_1159_);
lean_dec_ref(v_a_1141_);
v___x_1160_ = lean_apply_2(v_h__10_1132_, v_a_1158_, v_a_1159_);
return v___x_1160_;
}
}
}
case 4:
{
lean_object* v_a_1161_; lean_object* v___x_1162_; 
lean_dec(v_h__10_1132_);
lean_dec(v_h__9_1131_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_a_1161_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1161_);
lean_dec_ref(v_l_1122_);
v___x_1162_ = lean_apply_1(v_h__11_1133_, v_a_1161_);
return v___x_1162_;
}
default: 
{
lean_object* v_a_1163_; lean_object* v___x_1164_; 
lean_dec(v_h__11_1133_);
lean_dec(v_h__10_1132_);
lean_dec(v_h__8_1130_);
lean_dec(v_h__7_1129_);
lean_dec(v_h__6_1128_);
lean_dec(v_h__5_1127_);
lean_dec(v_h__4_1126_);
lean_dec(v_h__3_1125_);
lean_dec(v_h__2_1124_);
lean_dec(v_h__1_1123_);
v_a_1163_ = lean_ctor_get(v_l_1122_, 0);
lean_inc(v_a_1163_);
lean_dec_ref(v_l_1122_);
v___x_1164_ = lean_apply_1(v_h__9_1131_, v_a_1163_);
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__1_splitter___redArg(lean_object* v_x_1165_, lean_object* v_h__1_1166_, lean_object* v_h__2_1167_){
_start:
{
if (lean_obj_tag(v_x_1165_) == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_dec(v_h__1_1166_);
v___x_1168_ = lean_box(0);
v___x_1169_ = lean_apply_1(v_h__2_1167_, v___x_1168_);
return v___x_1169_;
}
else
{
lean_object* v_val_1170_; lean_object* v___x_1171_; 
lean_dec(v_h__2_1167_);
v_val_1170_ = lean_ctor_get(v_x_1165_, 0);
lean_inc(v_val_1170_);
lean_dec_ref(v_x_1165_);
v___x_1171_ = lean_apply_1(v_h__1_1166_, v_val_1170_);
return v___x_1171_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_normalizeAux_match__1_splitter(lean_object* v_motive_1172_, lean_object* v_x_1173_, lean_object* v_h__1_1174_, lean_object* v_h__2_1175_){
_start:
{
if (lean_obj_tag(v_x_1173_) == 0)
{
lean_object* v___x_1176_; lean_object* v___x_1177_; 
lean_dec(v_h__1_1174_);
v___x_1176_ = lean_box(0);
v___x_1177_ = lean_apply_1(v_h__2_1175_, v___x_1176_);
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; lean_object* v___x_1179_; 
lean_dec(v_h__2_1175_);
v_val_1178_ = lean_ctor_get(v_x_1173_, 0);
lean_inc(v_val_1178_);
lean_dec_ref(v_x_1173_);
v___x_1179_ = lean_apply_1(v_h__1_1174_, v_val_1178_);
return v___x_1179_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_subsumeVars(lean_object* v_x_1180_, lean_object* v_x_1181_){
_start:
{
if (lean_obj_tag(v_x_1180_) == 0)
{
lean_dec(v_x_1181_);
return v_x_1180_;
}
else
{
if (lean_obj_tag(v_x_1181_) == 0)
{
return v_x_1180_;
}
else
{
lean_object* v_head_1182_; lean_object* v_head_1183_; lean_object* v_tail_1184_; lean_object* v_tail_1185_; lean_object* v_var_1186_; lean_object* v_offset_1187_; lean_object* v_var_1188_; lean_object* v_offset_1189_; uint8_t v___x_1190_; 
v_head_1182_ = lean_ctor_get(v_x_1180_, 0);
v_head_1183_ = lean_ctor_get(v_x_1181_, 0);
v_tail_1184_ = lean_ctor_get(v_x_1180_, 1);
v_tail_1185_ = lean_ctor_get(v_x_1181_, 1);
v_var_1186_ = lean_ctor_get(v_head_1182_, 0);
v_offset_1187_ = lean_ctor_get(v_head_1182_, 1);
v_var_1188_ = lean_ctor_get(v_head_1183_, 0);
v_offset_1189_ = lean_ctor_get(v_head_1183_, 1);
v___x_1190_ = l_Lean_Name_cmp(v_var_1186_, v_var_1188_);
switch(v___x_1190_)
{
case 0:
{
lean_object* v___x_1192_; uint8_t v_isShared_1193_; uint8_t v_isSharedCheck_1198_; 
lean_inc(v_tail_1184_);
lean_inc(v_head_1182_);
v_isSharedCheck_1198_ = !lean_is_exclusive(v_x_1180_);
if (v_isSharedCheck_1198_ == 0)
{
lean_object* v_unused_1199_; lean_object* v_unused_1200_; 
v_unused_1199_ = lean_ctor_get(v_x_1180_, 1);
lean_dec(v_unused_1199_);
v_unused_1200_ = lean_ctor_get(v_x_1180_, 0);
lean_dec(v_unused_1200_);
v___x_1192_ = v_x_1180_;
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
else
{
lean_dec(v_x_1180_);
v___x_1192_ = lean_box(0);
v_isShared_1193_ = v_isSharedCheck_1198_;
goto v_resetjp_1191_;
}
v_resetjp_1191_:
{
lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1194_ = l_Lean_Level_Normalize_subsumeVars(v_tail_1184_, v_x_1181_);
if (v_isShared_1193_ == 0)
{
lean_ctor_set(v___x_1192_, 1, v___x_1194_);
v___x_1196_ = v___x_1192_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_head_1182_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v___x_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
}
case 1:
{
lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1210_; 
lean_inc(v_offset_1189_);
lean_inc(v_tail_1185_);
lean_inc(v_tail_1184_);
lean_inc(v_head_1182_);
lean_dec_ref(v_x_1180_);
v_isSharedCheck_1210_ = !lean_is_exclusive(v_x_1181_);
if (v_isSharedCheck_1210_ == 0)
{
lean_object* v_unused_1211_; lean_object* v_unused_1212_; 
v_unused_1211_ = lean_ctor_get(v_x_1181_, 1);
lean_dec(v_unused_1211_);
v_unused_1212_ = lean_ctor_get(v_x_1181_, 0);
lean_dec(v_unused_1212_);
v___x_1202_ = v_x_1181_;
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
else
{
lean_dec(v_x_1181_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1210_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
uint8_t v___x_1204_; 
v___x_1204_ = lean_nat_dec_le(v_offset_1187_, v_offset_1189_);
lean_dec(v_offset_1189_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; lean_object* v___x_1207_; 
v___x_1205_ = l_Lean_Level_Normalize_subsumeVars(v_tail_1184_, v_tail_1185_);
if (v_isShared_1203_ == 0)
{
lean_ctor_set(v___x_1202_, 1, v___x_1205_);
lean_ctor_set(v___x_1202_, 0, v_head_1182_);
v___x_1207_ = v___x_1202_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_head_1182_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v___x_1205_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
else
{
lean_del_object(v___x_1202_);
lean_dec(v_head_1182_);
v_x_1180_ = v_tail_1184_;
v_x_1181_ = v_tail_1185_;
goto _start;
}
}
}
default: 
{
lean_inc(v_tail_1185_);
lean_dec_ref(v_x_1181_);
v_x_1181_ = v_tail_1185_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subsumeVars_match__1_splitter___redArg(lean_object* v_x_1214_, lean_object* v_x_1215_, lean_object* v_h__1_1216_, lean_object* v_h__2_1217_, lean_object* v_h__3_1218_){
_start:
{
if (lean_obj_tag(v_x_1214_) == 0)
{
lean_object* v___x_1219_; 
lean_dec(v_h__3_1218_);
lean_dec(v_h__2_1217_);
v___x_1219_ = lean_apply_1(v_h__1_1216_, v_x_1215_);
return v___x_1219_;
}
else
{
lean_dec(v_h__1_1216_);
if (lean_obj_tag(v_x_1215_) == 0)
{
lean_object* v___x_1220_; 
lean_dec(v_h__3_1218_);
v___x_1220_ = lean_apply_2(v_h__2_1217_, v_x_1214_, lean_box(0));
return v___x_1220_;
}
else
{
lean_object* v_head_1221_; lean_object* v_tail_1222_; lean_object* v_head_1223_; lean_object* v_tail_1224_; lean_object* v___x_1225_; 
lean_dec(v_h__2_1217_);
v_head_1221_ = lean_ctor_get(v_x_1214_, 0);
lean_inc(v_head_1221_);
v_tail_1222_ = lean_ctor_get(v_x_1214_, 1);
lean_inc(v_tail_1222_);
lean_dec_ref(v_x_1214_);
v_head_1223_ = lean_ctor_get(v_x_1215_, 0);
lean_inc(v_head_1223_);
v_tail_1224_ = lean_ctor_get(v_x_1215_, 1);
lean_inc(v_tail_1224_);
lean_dec_ref(v_x_1215_);
v___x_1225_ = lean_apply_4(v_h__3_1218_, v_head_1221_, v_tail_1222_, v_head_1223_, v_tail_1224_);
return v___x_1225_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subsumeVars_match__1_splitter(lean_object* v_motive_1226_, lean_object* v_x_1227_, lean_object* v_x_1228_, lean_object* v_h__1_1229_, lean_object* v_h__2_1230_, lean_object* v_h__3_1231_){
_start:
{
if (lean_obj_tag(v_x_1227_) == 0)
{
lean_object* v___x_1232_; 
lean_dec(v_h__3_1231_);
lean_dec(v_h__2_1230_);
v___x_1232_ = lean_apply_1(v_h__1_1229_, v_x_1228_);
return v___x_1232_;
}
else
{
lean_dec(v_h__1_1229_);
if (lean_obj_tag(v_x_1228_) == 0)
{
lean_object* v___x_1233_; 
lean_dec(v_h__3_1231_);
v___x_1233_ = lean_apply_2(v_h__2_1230_, v_x_1227_, lean_box(0));
return v___x_1233_;
}
else
{
lean_object* v_head_1234_; lean_object* v_tail_1235_; lean_object* v_head_1236_; lean_object* v_tail_1237_; lean_object* v___x_1238_; 
lean_dec(v_h__2_1230_);
v_head_1234_ = lean_ctor_get(v_x_1227_, 0);
lean_inc(v_head_1234_);
v_tail_1235_ = lean_ctor_get(v_x_1227_, 1);
lean_inc(v_tail_1235_);
lean_dec_ref(v_x_1227_);
v_head_1236_ = lean_ctor_get(v_x_1228_, 0);
lean_inc(v_head_1236_);
v_tail_1237_ = lean_ctor_get(v_x_1228_, 1);
lean_inc(v_tail_1237_);
lean_dec_ref(v_x_1228_);
v___x_1238_ = lean_apply_4(v_h__3_1231_, v_head_1234_, v_tail_1235_, v_head_1236_, v_tail_1237_);
return v___x_1238_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter___redArg(uint8_t v_x_1239_, lean_object* v_h__1_1240_, lean_object* v_h__2_1241_, lean_object* v_h__3_1242_){
_start:
{
switch(v_x_1239_)
{
case 0:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
lean_dec(v_h__3_1242_);
lean_dec(v_h__2_1241_);
v___x_1243_ = lean_box(0);
v___x_1244_ = lean_apply_1(v_h__1_1240_, v___x_1243_);
return v___x_1244_;
}
case 1:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; 
lean_dec(v_h__3_1242_);
lean_dec(v_h__1_1240_);
v___x_1245_ = lean_box(0);
v___x_1246_ = lean_apply_1(v_h__2_1241_, v___x_1245_);
return v___x_1246_;
}
default: 
{
lean_object* v___x_1247_; lean_object* v___x_1248_; 
lean_dec(v_h__2_1241_);
lean_dec(v_h__1_1240_);
v___x_1247_ = lean_box(0);
v___x_1248_ = lean_apply_1(v_h__3_1242_, v___x_1247_);
return v___x_1248_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter___redArg___boxed(lean_object* v_x_1249_, lean_object* v_h__1_1250_, lean_object* v_h__2_1251_, lean_object* v_h__3_1252_){
_start:
{
uint8_t v_x_36__boxed_1253_; lean_object* v_res_1254_; 
v_x_36__boxed_1253_ = lean_unbox(v_x_1249_);
v_res_1254_ = l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter___redArg(v_x_36__boxed_1253_, v_h__1_1250_, v_h__2_1251_, v_h__3_1252_);
return v_res_1254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter(lean_object* v_motive_1255_, uint8_t v_x_1256_, lean_object* v_h__1_1257_, lean_object* v_h__2_1258_, lean_object* v_h__3_1259_){
_start:
{
switch(v_x_1256_)
{
case 0:
{
lean_object* v___x_1260_; lean_object* v___x_1261_; 
lean_dec(v_h__3_1259_);
lean_dec(v_h__2_1258_);
v___x_1260_ = lean_box(0);
v___x_1261_ = lean_apply_1(v_h__1_1257_, v___x_1260_);
return v___x_1261_;
}
case 1:
{
lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec(v_h__3_1259_);
lean_dec(v_h__1_1257_);
v___x_1262_ = lean_box(0);
v___x_1263_ = lean_apply_1(v_h__2_1258_, v___x_1262_);
return v___x_1263_;
}
default: 
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec(v_h__2_1258_);
lean_dec(v_h__1_1257_);
v___x_1264_ = lean_box(0);
v___x_1265_ = lean_apply_1(v_h__3_1259_, v___x_1264_);
return v___x_1265_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter___boxed(lean_object* v_motive_1266_, lean_object* v_x_1267_, lean_object* v_h__1_1268_, lean_object* v_h__2_1269_, lean_object* v_h__3_1270_){
_start:
{
uint8_t v_x_51__boxed_1271_; lean_object* v_res_1272_; 
v_x_51__boxed_1271_ = lean_unbox(v_x_1267_);
v_res_1272_ = l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_subset_match__1_splitter(v_motive_1266_, v_x_51__boxed_1271_, v_h__1_1268_, v_h__2_1269_, v_h__3_1270_);
return v_res_1272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_findParent(lean_object* v_f_1273_, lean_object* v_x_1274_, lean_object* v_x_1275_){
_start:
{
if (lean_obj_tag(v_x_1275_) == 0)
{
lean_dec(v_x_1274_);
lean_dec_ref(v_f_1273_);
return v_x_1275_;
}
else
{
lean_object* v_head_1276_; lean_object* v_tail_1277_; lean_object* v___x_1279_; uint8_t v_isShared_1280_; uint8_t v_isSharedCheck_1292_; 
v_head_1276_ = lean_ctor_get(v_x_1275_, 0);
v_tail_1277_ = lean_ctor_get(v_x_1275_, 1);
v_isSharedCheck_1292_ = !lean_is_exclusive(v_x_1275_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1279_ = v_x_1275_;
v_isShared_1280_ = v_isSharedCheck_1292_;
goto v_resetjp_1278_;
}
else
{
lean_inc(v_tail_1277_);
lean_inc(v_head_1276_);
lean_dec(v_x_1275_);
v___x_1279_ = lean_box(0);
v_isShared_1280_ = v_isSharedCheck_1292_;
goto v_resetjp_1278_;
}
v_resetjp_1278_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; 
lean_inc(v_tail_1277_);
lean_inc(v_x_1274_);
v___x_1281_ = l_List_reverseAux___redArg(v_x_1274_, v_tail_1277_);
lean_inc_ref(v_f_1273_);
v___x_1282_ = lean_apply_1(v_f_1273_, v___x_1281_);
v___x_1283_ = lean_unbox(v___x_1282_);
if (v___x_1283_ == 0)
{
lean_object* v___x_1285_; 
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v_x_1274_);
v___x_1285_ = v___x_1279_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_head_1276_);
lean_ctor_set(v_reuseFailAlloc_1287_, 1, v_x_1274_);
v___x_1285_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
v_x_1274_ = v___x_1285_;
v_x_1275_ = v_tail_1277_;
goto _start;
}
}
else
{
lean_object* v___x_1288_; lean_object* v___x_1290_; 
lean_dec(v_tail_1277_);
lean_dec(v_x_1274_);
lean_dec_ref(v_f_1273_);
v___x_1288_ = lean_box(0);
if (v_isShared_1280_ == 0)
{
lean_ctor_set(v___x_1279_, 1, v___x_1288_);
v___x_1290_ = v___x_1279_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_head_1276_);
lean_ctor_set(v_reuseFailAlloc_1291_, 1, v___x_1288_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___redArg(lean_object* v_k_1293_, lean_object* v_t_1294_){
_start:
{
if (lean_obj_tag(v_t_1294_) == 0)
{
lean_object* v_k_1295_; lean_object* v_l_1296_; lean_object* v_r_1297_; uint8_t v___x_1298_; 
v_k_1295_ = lean_ctor_get(v_t_1294_, 1);
v_l_1296_ = lean_ctor_get(v_t_1294_, 3);
v_r_1297_ = lean_ctor_get(v_t_1294_, 4);
v___x_1298_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_1293_, v_k_1295_);
switch(v___x_1298_)
{
case 0:
{
v_t_1294_ = v_l_1296_;
goto _start;
}
case 1:
{
uint8_t v___x_1300_; 
v___x_1300_ = 1;
return v___x_1300_;
}
default: 
{
v_t_1294_ = v_r_1297_;
goto _start;
}
}
}
else
{
uint8_t v___x_1302_; 
v___x_1302_ = 0;
return v___x_1302_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___redArg___boxed(lean_object* v_k_1303_, lean_object* v_t_1304_){
_start:
{
uint8_t v_res_1305_; lean_object* v_r_1306_; 
v_res_1305_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___redArg(v_k_1303_, v_t_1304_);
lean_dec(v_t_1304_);
lean_dec(v_k_1303_);
v_r_1306_ = lean_box(v_res_1305_);
return v_r_1306_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___lam__0(lean_object* v___x_1307_, lean_object* v___y_1308_){
_start:
{
uint8_t v___x_1309_; 
v___x_1309_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___redArg(v___y_1308_, v___x_1307_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___lam__0___boxed(lean_object* v___x_1310_, lean_object* v___y_1311_){
_start:
{
uint8_t v_res_1312_; lean_object* v_r_1313_; 
v_res_1312_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___lam__0(v___x_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec(v___x_1310_);
v_r_1313_ = lean_box(v_res_1312_);
return v_r_1313_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1___redArg(lean_object* v_k_1314_, lean_object* v_v_1315_, lean_object* v_t_1316_){
_start:
{
if (lean_obj_tag(v_t_1316_) == 0)
{
lean_object* v_size_1317_; lean_object* v_k_1318_; lean_object* v_v_1319_; lean_object* v_l_1320_; lean_object* v_r_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1601_; 
v_size_1317_ = lean_ctor_get(v_t_1316_, 0);
v_k_1318_ = lean_ctor_get(v_t_1316_, 1);
v_v_1319_ = lean_ctor_get(v_t_1316_, 2);
v_l_1320_ = lean_ctor_get(v_t_1316_, 3);
v_r_1321_ = lean_ctor_get(v_t_1316_, 4);
v_isSharedCheck_1601_ = !lean_is_exclusive(v_t_1316_);
if (v_isSharedCheck_1601_ == 0)
{
v___x_1323_ = v_t_1316_;
v_isShared_1324_ = v_isSharedCheck_1601_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_r_1321_);
lean_inc(v_l_1320_);
lean_inc(v_v_1319_);
lean_inc(v_k_1318_);
lean_inc(v_size_1317_);
lean_dec(v_t_1316_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1601_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
uint8_t v___x_1325_; 
v___x_1325_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_1314_, v_k_1318_);
switch(v___x_1325_)
{
case 0:
{
lean_object* v_impl_1326_; lean_object* v___x_1327_; 
lean_dec(v_size_1317_);
v_impl_1326_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1___redArg(v_k_1314_, v_v_1315_, v_l_1320_);
v___x_1327_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_1321_) == 0)
{
lean_object* v_size_1328_; lean_object* v_size_1329_; lean_object* v_k_1330_; lean_object* v_v_1331_; lean_object* v_l_1332_; lean_object* v_r_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_size_1328_ = lean_ctor_get(v_r_1321_, 0);
v_size_1329_ = lean_ctor_get(v_impl_1326_, 0);
lean_inc(v_size_1329_);
v_k_1330_ = lean_ctor_get(v_impl_1326_, 1);
lean_inc(v_k_1330_);
v_v_1331_ = lean_ctor_get(v_impl_1326_, 2);
lean_inc(v_v_1331_);
v_l_1332_ = lean_ctor_get(v_impl_1326_, 3);
lean_inc(v_l_1332_);
v_r_1333_ = lean_ctor_get(v_impl_1326_, 4);
lean_inc(v_r_1333_);
v___x_1334_ = lean_unsigned_to_nat(3u);
v___x_1335_ = lean_nat_mul(v___x_1334_, v_size_1328_);
v___x_1336_ = lean_nat_dec_lt(v___x_1335_, v_size_1329_);
lean_dec(v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1340_; 
lean_dec(v_r_1333_);
lean_dec(v_l_1332_);
lean_dec(v_v_1331_);
lean_dec(v_k_1330_);
v___x_1337_ = lean_nat_add(v___x_1327_, v_size_1329_);
lean_dec(v_size_1329_);
v___x_1338_ = lean_nat_add(v___x_1337_, v_size_1328_);
lean_dec(v___x_1337_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 3, v_impl_1326_);
lean_ctor_set(v___x_1323_, 0, v___x_1338_);
v___x_1340_ = v___x_1323_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v___x_1338_);
lean_ctor_set(v_reuseFailAlloc_1341_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1341_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1341_, 3, v_impl_1326_);
lean_ctor_set(v_reuseFailAlloc_1341_, 4, v_r_1321_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
else
{
lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1407_; 
v_isSharedCheck_1407_ = !lean_is_exclusive(v_impl_1326_);
if (v_isSharedCheck_1407_ == 0)
{
lean_object* v_unused_1408_; lean_object* v_unused_1409_; lean_object* v_unused_1410_; lean_object* v_unused_1411_; lean_object* v_unused_1412_; 
v_unused_1408_ = lean_ctor_get(v_impl_1326_, 4);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_impl_1326_, 3);
lean_dec(v_unused_1409_);
v_unused_1410_ = lean_ctor_get(v_impl_1326_, 2);
lean_dec(v_unused_1410_);
v_unused_1411_ = lean_ctor_get(v_impl_1326_, 1);
lean_dec(v_unused_1411_);
v_unused_1412_ = lean_ctor_get(v_impl_1326_, 0);
lean_dec(v_unused_1412_);
v___x_1343_ = v_impl_1326_;
v_isShared_1344_ = v_isSharedCheck_1407_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v_impl_1326_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1407_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_size_1345_; lean_object* v_size_1346_; lean_object* v_k_1347_; lean_object* v_v_1348_; lean_object* v_l_1349_; lean_object* v_r_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; uint8_t v___x_1353_; 
v_size_1345_ = lean_ctor_get(v_l_1332_, 0);
v_size_1346_ = lean_ctor_get(v_r_1333_, 0);
v_k_1347_ = lean_ctor_get(v_r_1333_, 1);
v_v_1348_ = lean_ctor_get(v_r_1333_, 2);
v_l_1349_ = lean_ctor_get(v_r_1333_, 3);
v_r_1350_ = lean_ctor_get(v_r_1333_, 4);
v___x_1351_ = lean_unsigned_to_nat(2u);
v___x_1352_ = lean_nat_mul(v___x_1351_, v_size_1345_);
v___x_1353_ = lean_nat_dec_lt(v_size_1346_, v___x_1352_);
lean_dec(v___x_1352_);
if (v___x_1353_ == 0)
{
lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1382_; 
lean_inc(v_r_1350_);
lean_inc(v_l_1349_);
lean_inc(v_v_1348_);
lean_inc(v_k_1347_);
v_isSharedCheck_1382_ = !lean_is_exclusive(v_r_1333_);
if (v_isSharedCheck_1382_ == 0)
{
lean_object* v_unused_1383_; lean_object* v_unused_1384_; lean_object* v_unused_1385_; lean_object* v_unused_1386_; lean_object* v_unused_1387_; 
v_unused_1383_ = lean_ctor_get(v_r_1333_, 4);
lean_dec(v_unused_1383_);
v_unused_1384_ = lean_ctor_get(v_r_1333_, 3);
lean_dec(v_unused_1384_);
v_unused_1385_ = lean_ctor_get(v_r_1333_, 2);
lean_dec(v_unused_1385_);
v_unused_1386_ = lean_ctor_get(v_r_1333_, 1);
lean_dec(v_unused_1386_);
v_unused_1387_ = lean_ctor_get(v_r_1333_, 0);
lean_dec(v_unused_1387_);
v___x_1355_ = v_r_1333_;
v_isShared_1356_ = v_isSharedCheck_1382_;
goto v_resetjp_1354_;
}
else
{
lean_dec(v_r_1333_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1382_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___y_1360_; lean_object* v___y_1361_; lean_object* v___y_1362_; lean_object* v___x_1370_; lean_object* v___y_1372_; 
v___x_1357_ = lean_nat_add(v___x_1327_, v_size_1329_);
lean_dec(v_size_1329_);
v___x_1358_ = lean_nat_add(v___x_1357_, v_size_1328_);
lean_dec(v___x_1357_);
v___x_1370_ = lean_nat_add(v___x_1327_, v_size_1345_);
if (lean_obj_tag(v_l_1349_) == 0)
{
lean_object* v_size_1380_; 
v_size_1380_ = lean_ctor_get(v_l_1349_, 0);
lean_inc(v_size_1380_);
v___y_1372_ = v_size_1380_;
goto v___jp_1371_;
}
else
{
lean_object* v___x_1381_; 
v___x_1381_ = lean_unsigned_to_nat(0u);
v___y_1372_ = v___x_1381_;
goto v___jp_1371_;
}
v___jp_1359_:
{
lean_object* v___x_1363_; lean_object* v___x_1365_; 
v___x_1363_ = lean_nat_add(v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec(v___y_1361_);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 4, v_r_1321_);
lean_ctor_set(v___x_1355_, 3, v_r_1350_);
lean_ctor_set(v___x_1355_, 2, v_v_1319_);
lean_ctor_set(v___x_1355_, 1, v_k_1318_);
lean_ctor_set(v___x_1355_, 0, v___x_1363_);
v___x_1365_ = v___x_1355_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v___x_1363_);
lean_ctor_set(v_reuseFailAlloc_1369_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1369_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1369_, 3, v_r_1350_);
lean_ctor_set(v_reuseFailAlloc_1369_, 4, v_r_1321_);
v___x_1365_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
lean_object* v___x_1367_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v___x_1365_);
lean_ctor_set(v___x_1343_, 3, v___y_1360_);
lean_ctor_set(v___x_1343_, 2, v_v_1348_);
lean_ctor_set(v___x_1343_, 1, v_k_1347_);
lean_ctor_set(v___x_1343_, 0, v___x_1358_);
v___x_1367_ = v___x_1343_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1358_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v_k_1347_);
lean_ctor_set(v_reuseFailAlloc_1368_, 2, v_v_1348_);
lean_ctor_set(v_reuseFailAlloc_1368_, 3, v___y_1360_);
lean_ctor_set(v_reuseFailAlloc_1368_, 4, v___x_1365_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
v___jp_1371_:
{
lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1373_ = lean_nat_add(v___x_1370_, v___y_1372_);
lean_dec(v___y_1372_);
lean_dec(v___x_1370_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_l_1349_);
lean_ctor_set(v___x_1323_, 3, v_l_1332_);
lean_ctor_set(v___x_1323_, 2, v_v_1331_);
lean_ctor_set(v___x_1323_, 1, v_k_1330_);
lean_ctor_set(v___x_1323_, 0, v___x_1373_);
v___x_1375_ = v___x_1323_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1373_);
lean_ctor_set(v_reuseFailAlloc_1379_, 1, v_k_1330_);
lean_ctor_set(v_reuseFailAlloc_1379_, 2, v_v_1331_);
lean_ctor_set(v_reuseFailAlloc_1379_, 3, v_l_1332_);
lean_ctor_set(v_reuseFailAlloc_1379_, 4, v_l_1349_);
v___x_1375_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
lean_object* v___x_1376_; 
v___x_1376_ = lean_nat_add(v___x_1327_, v_size_1328_);
if (lean_obj_tag(v_r_1350_) == 0)
{
lean_object* v_size_1377_; 
v_size_1377_ = lean_ctor_get(v_r_1350_, 0);
lean_inc(v_size_1377_);
v___y_1360_ = v___x_1375_;
v___y_1361_ = v___x_1376_;
v___y_1362_ = v_size_1377_;
goto v___jp_1359_;
}
else
{
lean_object* v___x_1378_; 
v___x_1378_ = lean_unsigned_to_nat(0u);
v___y_1360_ = v___x_1375_;
v___y_1361_ = v___x_1376_;
v___y_1362_ = v___x_1378_;
goto v___jp_1359_;
}
}
}
}
}
else
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1393_; 
lean_del_object(v___x_1323_);
v___x_1388_ = lean_nat_add(v___x_1327_, v_size_1329_);
lean_dec(v_size_1329_);
v___x_1389_ = lean_nat_add(v___x_1388_, v_size_1328_);
lean_dec(v___x_1388_);
v___x_1390_ = lean_nat_add(v___x_1327_, v_size_1328_);
v___x_1391_ = lean_nat_add(v___x_1390_, v_size_1346_);
lean_dec(v___x_1390_);
lean_inc_ref(v_r_1321_);
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 4, v_r_1321_);
lean_ctor_set(v___x_1343_, 3, v_r_1333_);
lean_ctor_set(v___x_1343_, 2, v_v_1319_);
lean_ctor_set(v___x_1343_, 1, v_k_1318_);
lean_ctor_set(v___x_1343_, 0, v___x_1391_);
v___x_1393_ = v___x_1343_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1391_);
lean_ctor_set(v_reuseFailAlloc_1406_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1406_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1406_, 3, v_r_1333_);
lean_ctor_set(v_reuseFailAlloc_1406_, 4, v_r_1321_);
v___x_1393_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1400_; 
v_isSharedCheck_1400_ = !lean_is_exclusive(v_r_1321_);
if (v_isSharedCheck_1400_ == 0)
{
lean_object* v_unused_1401_; lean_object* v_unused_1402_; lean_object* v_unused_1403_; lean_object* v_unused_1404_; lean_object* v_unused_1405_; 
v_unused_1401_ = lean_ctor_get(v_r_1321_, 4);
lean_dec(v_unused_1401_);
v_unused_1402_ = lean_ctor_get(v_r_1321_, 3);
lean_dec(v_unused_1402_);
v_unused_1403_ = lean_ctor_get(v_r_1321_, 2);
lean_dec(v_unused_1403_);
v_unused_1404_ = lean_ctor_get(v_r_1321_, 1);
lean_dec(v_unused_1404_);
v_unused_1405_ = lean_ctor_get(v_r_1321_, 0);
lean_dec(v_unused_1405_);
v___x_1395_ = v_r_1321_;
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
else
{
lean_dec(v_r_1321_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1400_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v___x_1398_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set(v___x_1395_, 4, v___x_1393_);
lean_ctor_set(v___x_1395_, 3, v_l_1332_);
lean_ctor_set(v___x_1395_, 2, v_v_1331_);
lean_ctor_set(v___x_1395_, 1, v_k_1330_);
lean_ctor_set(v___x_1395_, 0, v___x_1389_);
v___x_1398_ = v___x_1395_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1399_; 
v_reuseFailAlloc_1399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1399_, 0, v___x_1389_);
lean_ctor_set(v_reuseFailAlloc_1399_, 1, v_k_1330_);
lean_ctor_set(v_reuseFailAlloc_1399_, 2, v_v_1331_);
lean_ctor_set(v_reuseFailAlloc_1399_, 3, v_l_1332_);
lean_ctor_set(v_reuseFailAlloc_1399_, 4, v___x_1393_);
v___x_1398_ = v_reuseFailAlloc_1399_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
return v___x_1398_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1413_; 
v_l_1413_ = lean_ctor_get(v_impl_1326_, 3);
lean_inc(v_l_1413_);
if (lean_obj_tag(v_l_1413_) == 0)
{
lean_object* v_r_1414_; lean_object* v_k_1415_; lean_object* v_v_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1427_; 
v_r_1414_ = lean_ctor_get(v_impl_1326_, 4);
v_k_1415_ = lean_ctor_get(v_impl_1326_, 1);
v_v_1416_ = lean_ctor_get(v_impl_1326_, 2);
v_isSharedCheck_1427_ = !lean_is_exclusive(v_impl_1326_);
if (v_isSharedCheck_1427_ == 0)
{
lean_object* v_unused_1428_; lean_object* v_unused_1429_; 
v_unused_1428_ = lean_ctor_get(v_impl_1326_, 3);
lean_dec(v_unused_1428_);
v_unused_1429_ = lean_ctor_get(v_impl_1326_, 0);
lean_dec(v_unused_1429_);
v___x_1418_ = v_impl_1326_;
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_r_1414_);
lean_inc(v_v_1416_);
lean_inc(v_k_1415_);
lean_dec(v_impl_1326_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1427_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1420_; lean_object* v___x_1422_; 
v___x_1420_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_1414_);
if (v_isShared_1419_ == 0)
{
lean_ctor_set(v___x_1418_, 3, v_r_1414_);
lean_ctor_set(v___x_1418_, 2, v_v_1319_);
lean_ctor_set(v___x_1418_, 1, v_k_1318_);
lean_ctor_set(v___x_1418_, 0, v___x_1327_);
v___x_1422_ = v___x_1418_;
goto v_reusejp_1421_;
}
else
{
lean_object* v_reuseFailAlloc_1426_; 
v_reuseFailAlloc_1426_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1426_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1426_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1426_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1426_, 3, v_r_1414_);
lean_ctor_set(v_reuseFailAlloc_1426_, 4, v_r_1414_);
v___x_1422_ = v_reuseFailAlloc_1426_;
goto v_reusejp_1421_;
}
v_reusejp_1421_:
{
lean_object* v___x_1424_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v___x_1422_);
lean_ctor_set(v___x_1323_, 3, v_l_1413_);
lean_ctor_set(v___x_1323_, 2, v_v_1416_);
lean_ctor_set(v___x_1323_, 1, v_k_1415_);
lean_ctor_set(v___x_1323_, 0, v___x_1420_);
v___x_1424_ = v___x_1323_;
goto v_reusejp_1423_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1420_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v_k_1415_);
lean_ctor_set(v_reuseFailAlloc_1425_, 2, v_v_1416_);
lean_ctor_set(v_reuseFailAlloc_1425_, 3, v_l_1413_);
lean_ctor_set(v_reuseFailAlloc_1425_, 4, v___x_1422_);
v___x_1424_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1423_;
}
v_reusejp_1423_:
{
return v___x_1424_;
}
}
}
}
else
{
lean_object* v_r_1430_; 
v_r_1430_ = lean_ctor_get(v_impl_1326_, 4);
lean_inc(v_r_1430_);
if (lean_obj_tag(v_r_1430_) == 0)
{
lean_object* v_k_1431_; lean_object* v_v_1432_; lean_object* v___x_1434_; uint8_t v_isShared_1435_; uint8_t v_isSharedCheck_1455_; 
v_k_1431_ = lean_ctor_get(v_impl_1326_, 1);
v_v_1432_ = lean_ctor_get(v_impl_1326_, 2);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_impl_1326_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; lean_object* v_unused_1457_; lean_object* v_unused_1458_; 
v_unused_1456_ = lean_ctor_get(v_impl_1326_, 4);
lean_dec(v_unused_1456_);
v_unused_1457_ = lean_ctor_get(v_impl_1326_, 3);
lean_dec(v_unused_1457_);
v_unused_1458_ = lean_ctor_get(v_impl_1326_, 0);
lean_dec(v_unused_1458_);
v___x_1434_ = v_impl_1326_;
v_isShared_1435_ = v_isSharedCheck_1455_;
goto v_resetjp_1433_;
}
else
{
lean_inc(v_v_1432_);
lean_inc(v_k_1431_);
lean_dec(v_impl_1326_);
v___x_1434_ = lean_box(0);
v_isShared_1435_ = v_isSharedCheck_1455_;
goto v_resetjp_1433_;
}
v_resetjp_1433_:
{
lean_object* v_k_1436_; lean_object* v_v_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1451_; 
v_k_1436_ = lean_ctor_get(v_r_1430_, 1);
v_v_1437_ = lean_ctor_get(v_r_1430_, 2);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_r_1430_);
if (v_isSharedCheck_1451_ == 0)
{
lean_object* v_unused_1452_; lean_object* v_unused_1453_; lean_object* v_unused_1454_; 
v_unused_1452_ = lean_ctor_get(v_r_1430_, 4);
lean_dec(v_unused_1452_);
v_unused_1453_ = lean_ctor_get(v_r_1430_, 3);
lean_dec(v_unused_1453_);
v_unused_1454_ = lean_ctor_get(v_r_1430_, 0);
lean_dec(v_unused_1454_);
v___x_1439_ = v_r_1430_;
v_isShared_1440_ = v_isSharedCheck_1451_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_v_1437_);
lean_inc(v_k_1436_);
lean_dec(v_r_1430_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1451_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1441_; lean_object* v___x_1443_; 
v___x_1441_ = lean_unsigned_to_nat(3u);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 4, v_l_1413_);
lean_ctor_set(v___x_1439_, 3, v_l_1413_);
lean_ctor_set(v___x_1439_, 2, v_v_1432_);
lean_ctor_set(v___x_1439_, 1, v_k_1431_);
lean_ctor_set(v___x_1439_, 0, v___x_1327_);
v___x_1443_ = v___x_1439_;
goto v_reusejp_1442_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_k_1431_);
lean_ctor_set(v_reuseFailAlloc_1450_, 2, v_v_1432_);
lean_ctor_set(v_reuseFailAlloc_1450_, 3, v_l_1413_);
lean_ctor_set(v_reuseFailAlloc_1450_, 4, v_l_1413_);
v___x_1443_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1442_;
}
v_reusejp_1442_:
{
lean_object* v___x_1445_; 
if (v_isShared_1435_ == 0)
{
lean_ctor_set(v___x_1434_, 4, v_l_1413_);
lean_ctor_set(v___x_1434_, 2, v_v_1319_);
lean_ctor_set(v___x_1434_, 1, v_k_1318_);
lean_ctor_set(v___x_1434_, 0, v___x_1327_);
v___x_1445_ = v___x_1434_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1327_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1449_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1449_, 3, v_l_1413_);
lean_ctor_set(v_reuseFailAlloc_1449_, 4, v_l_1413_);
v___x_1445_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
lean_object* v___x_1447_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v___x_1445_);
lean_ctor_set(v___x_1323_, 3, v___x_1443_);
lean_ctor_set(v___x_1323_, 2, v_v_1437_);
lean_ctor_set(v___x_1323_, 1, v_k_1436_);
lean_ctor_set(v___x_1323_, 0, v___x_1441_);
v___x_1447_ = v___x_1323_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v___x_1441_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v_k_1436_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_v_1437_);
lean_ctor_set(v_reuseFailAlloc_1448_, 3, v___x_1443_);
lean_ctor_set(v_reuseFailAlloc_1448_, 4, v___x_1445_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
else
{
lean_object* v___x_1459_; lean_object* v___x_1461_; 
v___x_1459_ = lean_unsigned_to_nat(2u);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_r_1430_);
lean_ctor_set(v___x_1323_, 3, v_impl_1326_);
lean_ctor_set(v___x_1323_, 0, v___x_1459_);
v___x_1461_ = v___x_1323_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1459_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_impl_1326_);
lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_r_1430_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
}
}
case 1:
{
lean_object* v___x_1464_; 
lean_dec(v_v_1319_);
lean_dec(v_k_1318_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 2, v_v_1315_);
lean_ctor_set(v___x_1323_, 1, v_k_1314_);
v___x_1464_ = v___x_1323_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_size_1317_);
lean_ctor_set(v_reuseFailAlloc_1465_, 1, v_k_1314_);
lean_ctor_set(v_reuseFailAlloc_1465_, 2, v_v_1315_);
lean_ctor_set(v_reuseFailAlloc_1465_, 3, v_l_1320_);
lean_ctor_set(v_reuseFailAlloc_1465_, 4, v_r_1321_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
default: 
{
lean_object* v_impl_1466_; lean_object* v___x_1467_; 
lean_dec(v_size_1317_);
v_impl_1466_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1___redArg(v_k_1314_, v_v_1315_, v_r_1321_);
v___x_1467_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_1320_) == 0)
{
lean_object* v_size_1468_; lean_object* v_size_1469_; lean_object* v_k_1470_; lean_object* v_v_1471_; lean_object* v_l_1472_; lean_object* v_r_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; uint8_t v___x_1476_; 
v_size_1468_ = lean_ctor_get(v_l_1320_, 0);
v_size_1469_ = lean_ctor_get(v_impl_1466_, 0);
lean_inc(v_size_1469_);
v_k_1470_ = lean_ctor_get(v_impl_1466_, 1);
lean_inc(v_k_1470_);
v_v_1471_ = lean_ctor_get(v_impl_1466_, 2);
lean_inc(v_v_1471_);
v_l_1472_ = lean_ctor_get(v_impl_1466_, 3);
lean_inc(v_l_1472_);
v_r_1473_ = lean_ctor_get(v_impl_1466_, 4);
lean_inc(v_r_1473_);
v___x_1474_ = lean_unsigned_to_nat(3u);
v___x_1475_ = lean_nat_mul(v___x_1474_, v_size_1468_);
v___x_1476_ = lean_nat_dec_lt(v___x_1475_, v_size_1469_);
lean_dec(v___x_1475_);
if (v___x_1476_ == 0)
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1480_; 
lean_dec(v_r_1473_);
lean_dec(v_l_1472_);
lean_dec(v_v_1471_);
lean_dec(v_k_1470_);
v___x_1477_ = lean_nat_add(v___x_1467_, v_size_1468_);
v___x_1478_ = lean_nat_add(v___x_1477_, v_size_1469_);
lean_dec(v_size_1469_);
lean_dec(v___x_1477_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_impl_1466_);
lean_ctor_set(v___x_1323_, 0, v___x_1478_);
v___x_1480_ = v___x_1323_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1481_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1481_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1481_, 3, v_l_1320_);
lean_ctor_set(v_reuseFailAlloc_1481_, 4, v_impl_1466_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
else
{
lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1545_; 
v_isSharedCheck_1545_ = !lean_is_exclusive(v_impl_1466_);
if (v_isSharedCheck_1545_ == 0)
{
lean_object* v_unused_1546_; lean_object* v_unused_1547_; lean_object* v_unused_1548_; lean_object* v_unused_1549_; lean_object* v_unused_1550_; 
v_unused_1546_ = lean_ctor_get(v_impl_1466_, 4);
lean_dec(v_unused_1546_);
v_unused_1547_ = lean_ctor_get(v_impl_1466_, 3);
lean_dec(v_unused_1547_);
v_unused_1548_ = lean_ctor_get(v_impl_1466_, 2);
lean_dec(v_unused_1548_);
v_unused_1549_ = lean_ctor_get(v_impl_1466_, 1);
lean_dec(v_unused_1549_);
v_unused_1550_ = lean_ctor_get(v_impl_1466_, 0);
lean_dec(v_unused_1550_);
v___x_1483_ = v_impl_1466_;
v_isShared_1484_ = v_isSharedCheck_1545_;
goto v_resetjp_1482_;
}
else
{
lean_dec(v_impl_1466_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1545_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v_size_1485_; lean_object* v_k_1486_; lean_object* v_v_1487_; lean_object* v_l_1488_; lean_object* v_r_1489_; lean_object* v_size_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v_size_1485_ = lean_ctor_get(v_l_1472_, 0);
v_k_1486_ = lean_ctor_get(v_l_1472_, 1);
v_v_1487_ = lean_ctor_get(v_l_1472_, 2);
v_l_1488_ = lean_ctor_get(v_l_1472_, 3);
v_r_1489_ = lean_ctor_get(v_l_1472_, 4);
v_size_1490_ = lean_ctor_get(v_r_1473_, 0);
v___x_1491_ = lean_unsigned_to_nat(2u);
v___x_1492_ = lean_nat_mul(v___x_1491_, v_size_1490_);
v___x_1493_ = lean_nat_dec_lt(v_size_1485_, v___x_1492_);
lean_dec(v___x_1492_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1521_; 
lean_inc(v_r_1489_);
lean_inc(v_l_1488_);
lean_inc(v_v_1487_);
lean_inc(v_k_1486_);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_l_1472_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; lean_object* v_unused_1525_; lean_object* v_unused_1526_; 
v_unused_1522_ = lean_ctor_get(v_l_1472_, 4);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_l_1472_, 3);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_l_1472_, 2);
lean_dec(v_unused_1524_);
v_unused_1525_ = lean_ctor_get(v_l_1472_, 1);
lean_dec(v_unused_1525_);
v_unused_1526_ = lean_ctor_get(v_l_1472_, 0);
lean_dec(v_unused_1526_);
v___x_1495_ = v_l_1472_;
v_isShared_1496_ = v_isSharedCheck_1521_;
goto v_resetjp_1494_;
}
else
{
lean_dec(v_l_1472_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1521_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___y_1500_; lean_object* v___y_1501_; lean_object* v___y_1502_; lean_object* v___y_1511_; 
v___x_1497_ = lean_nat_add(v___x_1467_, v_size_1468_);
v___x_1498_ = lean_nat_add(v___x_1497_, v_size_1469_);
lean_dec(v_size_1469_);
if (lean_obj_tag(v_l_1488_) == 0)
{
lean_object* v_size_1519_; 
v_size_1519_ = lean_ctor_get(v_l_1488_, 0);
lean_inc(v_size_1519_);
v___y_1511_ = v_size_1519_;
goto v___jp_1510_;
}
else
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_unsigned_to_nat(0u);
v___y_1511_ = v___x_1520_;
goto v___jp_1510_;
}
v___jp_1499_:
{
lean_object* v___x_1503_; lean_object* v___x_1505_; 
v___x_1503_ = lean_nat_add(v___y_1501_, v___y_1502_);
lean_dec(v___y_1502_);
lean_dec(v___y_1501_);
if (v_isShared_1496_ == 0)
{
lean_ctor_set(v___x_1495_, 4, v_r_1473_);
lean_ctor_set(v___x_1495_, 3, v_r_1489_);
lean_ctor_set(v___x_1495_, 2, v_v_1471_);
lean_ctor_set(v___x_1495_, 1, v_k_1470_);
lean_ctor_set(v___x_1495_, 0, v___x_1503_);
v___x_1505_ = v___x_1495_;
goto v_reusejp_1504_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1503_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_r_1489_);
lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_r_1473_);
v___x_1505_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1504_;
}
v_reusejp_1504_:
{
lean_object* v___x_1507_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v___x_1505_);
lean_ctor_set(v___x_1483_, 3, v___y_1500_);
lean_ctor_set(v___x_1483_, 2, v_v_1487_);
lean_ctor_set(v___x_1483_, 1, v_k_1486_);
lean_ctor_set(v___x_1483_, 0, v___x_1498_);
v___x_1507_ = v___x_1483_;
goto v_reusejp_1506_;
}
else
{
lean_object* v_reuseFailAlloc_1508_; 
v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1498_);
lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1486_);
lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1487_);
lean_ctor_set(v_reuseFailAlloc_1508_, 3, v___y_1500_);
lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1505_);
v___x_1507_ = v_reuseFailAlloc_1508_;
goto v_reusejp_1506_;
}
v_reusejp_1506_:
{
return v___x_1507_;
}
}
}
v___jp_1510_:
{
lean_object* v___x_1512_; lean_object* v___x_1514_; 
v___x_1512_ = lean_nat_add(v___x_1497_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec(v___x_1497_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_l_1488_);
lean_ctor_set(v___x_1323_, 0, v___x_1512_);
v___x_1514_ = v___x_1323_;
goto v_reusejp_1513_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1512_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1518_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1518_, 3, v_l_1320_);
lean_ctor_set(v_reuseFailAlloc_1518_, 4, v_l_1488_);
v___x_1514_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1513_;
}
v_reusejp_1513_:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_nat_add(v___x_1467_, v_size_1490_);
if (lean_obj_tag(v_r_1489_) == 0)
{
lean_object* v_size_1516_; 
v_size_1516_ = lean_ctor_get(v_r_1489_, 0);
lean_inc(v_size_1516_);
v___y_1500_ = v___x_1514_;
v___y_1501_ = v___x_1515_;
v___y_1502_ = v_size_1516_;
goto v___jp_1499_;
}
else
{
lean_object* v___x_1517_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
v___y_1500_ = v___x_1514_;
v___y_1501_ = v___x_1515_;
v___y_1502_ = v___x_1517_;
goto v___jp_1499_;
}
}
}
}
}
else
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1531_; 
lean_del_object(v___x_1323_);
v___x_1527_ = lean_nat_add(v___x_1467_, v_size_1468_);
v___x_1528_ = lean_nat_add(v___x_1527_, v_size_1469_);
lean_dec(v_size_1469_);
v___x_1529_ = lean_nat_add(v___x_1527_, v_size_1485_);
lean_dec(v___x_1527_);
lean_inc_ref(v_l_1320_);
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 4, v_l_1472_);
lean_ctor_set(v___x_1483_, 3, v_l_1320_);
lean_ctor_set(v___x_1483_, 2, v_v_1319_);
lean_ctor_set(v___x_1483_, 1, v_k_1318_);
lean_ctor_set(v___x_1483_, 0, v___x_1529_);
v___x_1531_ = v___x_1483_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1544_; 
v_reuseFailAlloc_1544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1544_, 0, v___x_1529_);
lean_ctor_set(v_reuseFailAlloc_1544_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1544_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1544_, 3, v_l_1320_);
lean_ctor_set(v_reuseFailAlloc_1544_, 4, v_l_1472_);
v___x_1531_ = v_reuseFailAlloc_1544_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1538_; 
v_isSharedCheck_1538_ = !lean_is_exclusive(v_l_1320_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; lean_object* v_unused_1540_; lean_object* v_unused_1541_; lean_object* v_unused_1542_; lean_object* v_unused_1543_; 
v_unused_1539_ = lean_ctor_get(v_l_1320_, 4);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_l_1320_, 3);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_l_1320_, 2);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_l_1320_, 1);
lean_dec(v_unused_1542_);
v_unused_1543_ = lean_ctor_get(v_l_1320_, 0);
lean_dec(v_unused_1543_);
v___x_1533_ = v_l_1320_;
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v_l_1320_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1538_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1536_; 
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 4, v_r_1473_);
lean_ctor_set(v___x_1533_, 3, v___x_1531_);
lean_ctor_set(v___x_1533_, 2, v_v_1471_);
lean_ctor_set(v___x_1533_, 1, v_k_1470_);
lean_ctor_set(v___x_1533_, 0, v___x_1528_);
v___x_1536_ = v___x_1533_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v___x_1528_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_k_1470_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v_v_1471_);
lean_ctor_set(v_reuseFailAlloc_1537_, 3, v___x_1531_);
lean_ctor_set(v_reuseFailAlloc_1537_, 4, v_r_1473_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_1551_; 
v_l_1551_ = lean_ctor_get(v_impl_1466_, 3);
lean_inc(v_l_1551_);
if (lean_obj_tag(v_l_1551_) == 0)
{
lean_object* v_r_1552_; lean_object* v_k_1553_; lean_object* v_v_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1577_; 
v_r_1552_ = lean_ctor_get(v_impl_1466_, 4);
v_k_1553_ = lean_ctor_get(v_impl_1466_, 1);
v_v_1554_ = lean_ctor_get(v_impl_1466_, 2);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_impl_1466_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; lean_object* v_unused_1579_; 
v_unused_1578_ = lean_ctor_get(v_impl_1466_, 3);
lean_dec(v_unused_1578_);
v_unused_1579_ = lean_ctor_get(v_impl_1466_, 0);
lean_dec(v_unused_1579_);
v___x_1556_ = v_impl_1466_;
v_isShared_1557_ = v_isSharedCheck_1577_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_r_1552_);
lean_inc(v_v_1554_);
lean_inc(v_k_1553_);
lean_dec(v_impl_1466_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1577_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v_k_1558_; lean_object* v_v_1559_; lean_object* v___x_1561_; uint8_t v_isShared_1562_; uint8_t v_isSharedCheck_1573_; 
v_k_1558_ = lean_ctor_get(v_l_1551_, 1);
v_v_1559_ = lean_ctor_get(v_l_1551_, 2);
v_isSharedCheck_1573_ = !lean_is_exclusive(v_l_1551_);
if (v_isSharedCheck_1573_ == 0)
{
lean_object* v_unused_1574_; lean_object* v_unused_1575_; lean_object* v_unused_1576_; 
v_unused_1574_ = lean_ctor_get(v_l_1551_, 4);
lean_dec(v_unused_1574_);
v_unused_1575_ = lean_ctor_get(v_l_1551_, 3);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_l_1551_, 0);
lean_dec(v_unused_1576_);
v___x_1561_ = v_l_1551_;
v_isShared_1562_ = v_isSharedCheck_1573_;
goto v_resetjp_1560_;
}
else
{
lean_inc(v_v_1559_);
lean_inc(v_k_1558_);
lean_dec(v_l_1551_);
v___x_1561_ = lean_box(0);
v_isShared_1562_ = v_isSharedCheck_1573_;
goto v_resetjp_1560_;
}
v_resetjp_1560_:
{
lean_object* v___x_1563_; lean_object* v___x_1565_; 
v___x_1563_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_1552_, 2);
if (v_isShared_1562_ == 0)
{
lean_ctor_set(v___x_1561_, 4, v_r_1552_);
lean_ctor_set(v___x_1561_, 3, v_r_1552_);
lean_ctor_set(v___x_1561_, 2, v_v_1319_);
lean_ctor_set(v___x_1561_, 1, v_k_1318_);
lean_ctor_set(v___x_1561_, 0, v___x_1467_);
v___x_1565_ = v___x_1561_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1572_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1572_, 3, v_r_1552_);
lean_ctor_set(v_reuseFailAlloc_1572_, 4, v_r_1552_);
v___x_1565_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
lean_object* v___x_1567_; 
lean_inc(v_r_1552_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 3, v_r_1552_);
lean_ctor_set(v___x_1556_, 0, v___x_1467_);
v___x_1567_ = v___x_1556_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1571_; 
v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1571_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1571_, 1, v_k_1553_);
lean_ctor_set(v_reuseFailAlloc_1571_, 2, v_v_1554_);
lean_ctor_set(v_reuseFailAlloc_1571_, 3, v_r_1552_);
lean_ctor_set(v_reuseFailAlloc_1571_, 4, v_r_1552_);
v___x_1567_ = v_reuseFailAlloc_1571_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
lean_object* v___x_1569_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v___x_1567_);
lean_ctor_set(v___x_1323_, 3, v___x_1565_);
lean_ctor_set(v___x_1323_, 2, v_v_1559_);
lean_ctor_set(v___x_1323_, 1, v_k_1558_);
lean_ctor_set(v___x_1323_, 0, v___x_1563_);
v___x_1569_ = v___x_1323_;
goto v_reusejp_1568_;
}
else
{
lean_object* v_reuseFailAlloc_1570_; 
v_reuseFailAlloc_1570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1570_, 0, v___x_1563_);
lean_ctor_set(v_reuseFailAlloc_1570_, 1, v_k_1558_);
lean_ctor_set(v_reuseFailAlloc_1570_, 2, v_v_1559_);
lean_ctor_set(v_reuseFailAlloc_1570_, 3, v___x_1565_);
lean_ctor_set(v_reuseFailAlloc_1570_, 4, v___x_1567_);
v___x_1569_ = v_reuseFailAlloc_1570_;
goto v_reusejp_1568_;
}
v_reusejp_1568_:
{
return v___x_1569_;
}
}
}
}
}
}
else
{
lean_object* v_r_1580_; 
v_r_1580_ = lean_ctor_get(v_impl_1466_, 4);
lean_inc(v_r_1580_);
if (lean_obj_tag(v_r_1580_) == 0)
{
lean_object* v_k_1581_; lean_object* v_v_1582_; lean_object* v___x_1584_; uint8_t v_isShared_1585_; uint8_t v_isSharedCheck_1593_; 
v_k_1581_ = lean_ctor_get(v_impl_1466_, 1);
v_v_1582_ = lean_ctor_get(v_impl_1466_, 2);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_impl_1466_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; lean_object* v_unused_1595_; lean_object* v_unused_1596_; 
v_unused_1594_ = lean_ctor_get(v_impl_1466_, 4);
lean_dec(v_unused_1594_);
v_unused_1595_ = lean_ctor_get(v_impl_1466_, 3);
lean_dec(v_unused_1595_);
v_unused_1596_ = lean_ctor_get(v_impl_1466_, 0);
lean_dec(v_unused_1596_);
v___x_1584_ = v_impl_1466_;
v_isShared_1585_ = v_isSharedCheck_1593_;
goto v_resetjp_1583_;
}
else
{
lean_inc(v_v_1582_);
lean_inc(v_k_1581_);
lean_dec(v_impl_1466_);
v___x_1584_ = lean_box(0);
v_isShared_1585_ = v_isSharedCheck_1593_;
goto v_resetjp_1583_;
}
v_resetjp_1583_:
{
lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1586_ = lean_unsigned_to_nat(3u);
if (v_isShared_1585_ == 0)
{
lean_ctor_set(v___x_1584_, 4, v_l_1551_);
lean_ctor_set(v___x_1584_, 2, v_v_1319_);
lean_ctor_set(v___x_1584_, 1, v_k_1318_);
lean_ctor_set(v___x_1584_, 0, v___x_1467_);
v___x_1588_ = v___x_1584_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v___x_1467_);
lean_ctor_set(v_reuseFailAlloc_1592_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1592_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1592_, 3, v_l_1551_);
lean_ctor_set(v_reuseFailAlloc_1592_, 4, v_l_1551_);
v___x_1588_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1590_; 
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_r_1580_);
lean_ctor_set(v___x_1323_, 3, v___x_1588_);
lean_ctor_set(v___x_1323_, 2, v_v_1582_);
lean_ctor_set(v___x_1323_, 1, v_k_1581_);
lean_ctor_set(v___x_1323_, 0, v___x_1586_);
v___x_1590_ = v___x_1323_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_k_1581_);
lean_ctor_set(v_reuseFailAlloc_1591_, 2, v_v_1582_);
lean_ctor_set(v_reuseFailAlloc_1591_, 3, v___x_1588_);
lean_ctor_set(v_reuseFailAlloc_1591_, 4, v_r_1580_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
else
{
lean_object* v___x_1597_; lean_object* v___x_1599_; 
v___x_1597_ = lean_unsigned_to_nat(2u);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 4, v_impl_1466_);
lean_ctor_set(v___x_1323_, 3, v_r_1580_);
lean_ctor_set(v___x_1323_, 0, v___x_1597_);
v___x_1599_ = v___x_1323_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1600_; 
v_reuseFailAlloc_1600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1600_, 1, v_k_1318_);
lean_ctor_set(v_reuseFailAlloc_1600_, 2, v_v_1319_);
lean_ctor_set(v_reuseFailAlloc_1600_, 3, v_r_1580_);
lean_ctor_set(v_reuseFailAlloc_1600_, 4, v_impl_1466_);
v___x_1599_ = v_reuseFailAlloc_1600_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
return v___x_1599_;
}
}
}
}
}
}
}
}
else
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
v___x_1602_ = lean_unsigned_to_nat(1u);
v___x_1603_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
lean_ctor_set(v___x_1603_, 1, v_k_1314_);
lean_ctor_set(v___x_1603_, 2, v_v_1315_);
lean_ctor_set(v___x_1603_, 3, v_t_1316_);
lean_ctor_set(v___x_1603_, 4, v_t_1316_);
return v___x_1603_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__0(lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
if (lean_obj_tag(v_x_1605_) == 0)
{
lean_inc(v_x_1604_);
return v_x_1604_;
}
else
{
lean_object* v_head_1606_; lean_object* v_tail_1607_; lean_object* v_offset_1608_; uint8_t v___x_1609_; 
v_head_1606_ = lean_ctor_get(v_x_1605_, 0);
v_tail_1607_ = lean_ctor_get(v_x_1605_, 1);
v_offset_1608_ = lean_ctor_get(v_head_1606_, 1);
v___x_1609_ = lean_nat_dec_le(v_x_1604_, v_offset_1608_);
if (v___x_1609_ == 0)
{
v_x_1605_ = v_tail_1607_;
goto _start;
}
else
{
v_x_1604_ = v_offset_1608_;
v_x_1605_ = v_tail_1607_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__0___boxed(lean_object* v_x_1612_, lean_object* v_x_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_List_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__0(v_x_1612_, v_x_1613_);
lean_dec(v_x_1613_);
lean_dec(v_x_1612_);
return v_res_1614_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__2_spec__2(lean_object* v_p_u2081_1615_, lean_object* v_init_1616_, lean_object* v_x_1617_){
_start:
{
if (lean_obj_tag(v_x_1617_) == 0)
{
lean_object* v_k_1618_; lean_object* v_v_1619_; lean_object* v_l_1620_; lean_object* v_r_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; uint8_t v___x_1624_; 
v_k_1618_ = lean_ctor_get(v_x_1617_, 1);
lean_inc_n(v_k_1618_, 2);
v_v_1619_ = lean_ctor_get(v_x_1617_, 2);
lean_inc(v_v_1619_);
v_l_1620_ = lean_ctor_get(v_x_1617_, 3);
lean_inc(v_l_1620_);
v_r_1621_ = lean_ctor_get(v_x_1617_, 4);
lean_inc(v_r_1621_);
lean_dec_ref(v_x_1617_);
lean_inc_n(v_p_u2081_1615_, 2);
v___x_1622_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__2_spec__2(v_p_u2081_1615_, v_init_1616_, v_l_1620_);
v___x_1623_ = ((lean_object*)(l_Lean_Level_Normalize_instOrdName___closed__0));
v___x_1624_ = l_Lean_Level_Normalize_subset___redArg(v___x_1623_, v_k_1618_, v_p_u2081_1615_);
if (v___x_1624_ == 0)
{
lean_dec(v_v_1619_);
lean_dec(v_k_1618_);
v_init_1616_ = v___x_1622_;
v_x_1617_ = v_r_1621_;
goto _start;
}
else
{
lean_object* v_path_1626_; lean_object* v_const_1627_; lean_object* v_var_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; uint8_t v_same_1631_; lean_object* v___y_1633_; lean_object* v___x_1650_; uint8_t v___y_1652_; uint8_t v___x_1670_; 
v_path_1626_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_path_1626_);
v_const_1627_ = lean_ctor_get(v___x_1622_, 1);
lean_inc(v_const_1627_);
v_var_1628_ = lean_ctor_get(v___x_1622_, 2);
lean_inc(v_var_1628_);
v___x_1629_ = l_List_lengthTR___redArg(v_p_u2081_1615_);
v___x_1630_ = l_List_lengthTR___redArg(v_k_1618_);
lean_dec(v_k_1618_);
v_same_1631_ = lean_nat_dec_eq(v___x_1629_, v___x_1630_);
lean_dec(v___x_1630_);
lean_dec(v___x_1629_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1670_ = lean_nat_dec_eq(v_const_1627_, v___x_1650_);
if (v___x_1670_ == 0)
{
if (v_same_1631_ == 0)
{
lean_object* v_const_1671_; uint8_t v___x_1672_; 
v_const_1671_ = lean_ctor_get(v_v_1619_, 1);
v___x_1672_ = lean_nat_dec_lt(v_const_1671_, v_const_1627_);
if (v___x_1672_ == 0)
{
lean_dec(v_const_1627_);
v___y_1652_ = v___x_1672_;
goto v___jp_1651_;
}
else
{
goto v___jp_1663_;
}
}
else
{
goto v___jp_1663_;
}
}
else
{
lean_dec(v_const_1627_);
v___y_1652_ = v___x_1624_;
goto v___jp_1651_;
}
v___jp_1632_:
{
if (v_same_1631_ == 0)
{
lean_object* v_var_1634_; uint8_t v___x_1635_; 
v_var_1634_ = lean_ctor_get(v_v_1619_, 2);
lean_inc(v_var_1634_);
lean_dec(v_v_1619_);
v___x_1635_ = l_List_isEmpty___redArg(v_var_1634_);
if (v___x_1635_ == 0)
{
lean_object* v_path_1636_; lean_object* v_const_1637_; lean_object* v_var_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1647_; 
v_path_1636_ = lean_ctor_get(v___y_1633_, 0);
v_const_1637_ = lean_ctor_get(v___y_1633_, 1);
v_var_1638_ = lean_ctor_get(v___y_1633_, 2);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___y_1633_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1640_ = v___y_1633_;
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_var_1638_);
lean_inc(v_const_1637_);
lean_inc(v_path_1636_);
lean_dec(v___y_1633_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1647_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; lean_object* v___x_1644_; 
v___x_1642_ = l_Lean_Level_Normalize_subsumeVars(v_var_1638_, v_var_1634_);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 2, v___x_1642_);
v___x_1644_ = v___x_1640_;
goto v_reusejp_1643_;
}
else
{
lean_object* v_reuseFailAlloc_1646_; 
v_reuseFailAlloc_1646_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1646_, 0, v_path_1636_);
lean_ctor_set(v_reuseFailAlloc_1646_, 1, v_const_1637_);
lean_ctor_set(v_reuseFailAlloc_1646_, 2, v___x_1642_);
v___x_1644_ = v_reuseFailAlloc_1646_;
goto v_reusejp_1643_;
}
v_reusejp_1643_:
{
v_init_1616_ = v___x_1644_;
v_x_1617_ = v_r_1621_;
goto _start;
}
}
}
else
{
lean_dec(v_var_1634_);
v_init_1616_ = v___y_1633_;
v_x_1617_ = v_r_1621_;
goto _start;
}
}
else
{
lean_dec(v_v_1619_);
v_init_1616_ = v___y_1633_;
v_x_1617_ = v_r_1621_;
goto _start;
}
}
v___jp_1651_:
{
if (v___y_1652_ == 0)
{
lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1659_; 
v_isSharedCheck_1659_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; 
v_unused_1660_ = lean_ctor_get(v___x_1622_, 2);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v___x_1622_, 1);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v___x_1622_, 0);
lean_dec(v_unused_1662_);
v___x_1654_ = v___x_1622_;
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
else
{
lean_dec(v___x_1622_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1659_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 1, v___x_1650_);
v___x_1657_ = v___x_1654_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_path_1626_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v___x_1650_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v_var_1628_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
v___y_1633_ = v___x_1657_;
goto v___jp_1632_;
}
}
}
else
{
lean_dec(v_var_1628_);
lean_dec(v_path_1626_);
v___y_1633_ = v___x_1622_;
goto v___jp_1632_;
}
}
v___jp_1663_:
{
lean_object* v_var_1664_; uint8_t v___x_1665_; 
v_var_1664_ = lean_ctor_get(v_v_1619_, 2);
v___x_1665_ = l_List_isEmpty___redArg(v_var_1664_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1666_ = l_List_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__0(v___x_1650_, v_var_1628_);
v___x_1667_ = lean_unsigned_to_nat(1u);
v___x_1668_ = lean_nat_add(v___x_1666_, v___x_1667_);
lean_dec(v___x_1666_);
v___x_1669_ = lean_nat_dec_lt(v___x_1668_, v_const_1627_);
lean_dec(v_const_1627_);
lean_dec(v___x_1668_);
v___y_1652_ = v___x_1669_;
goto v___jp_1651_;
}
else
{
lean_dec(v_const_1627_);
v___y_1652_ = v___x_1624_;
goto v___jp_1651_;
}
}
}
}
else
{
lean_dec(v_p_u2081_1615_);
return v_init_1616_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5(uint8_t v_paths_1673_, lean_object* v_init_1674_, lean_object* v_x_1675_){
_start:
{
if (lean_obj_tag(v_x_1675_) == 0)
{
lean_object* v_k_1676_; lean_object* v_v_1677_; lean_object* v_l_1678_; lean_object* v_r_1679_; lean_object* v___x_1680_; lean_object* v___y_1682_; lean_object* v_n_u2081_1685_; 
v_k_1676_ = lean_ctor_get(v_x_1675_, 1);
lean_inc_n(v_k_1676_, 2);
v_v_1677_ = lean_ctor_get(v_x_1675_, 2);
lean_inc(v_v_1677_);
v_l_1678_ = lean_ctor_get(v_x_1675_, 3);
lean_inc(v_l_1678_);
v_r_1679_ = lean_ctor_get(v_x_1675_, 4);
lean_inc(v_r_1679_);
lean_dec_ref(v_x_1675_);
v___x_1680_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5(v_paths_1673_, v_init_1674_, v_l_1678_);
lean_inc(v___x_1680_);
v_n_u2081_1685_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__2_spec__2(v_k_1676_, v_v_1677_, v___x_1680_);
if (v_paths_1673_ == 0)
{
v___y_1682_ = v_n_u2081_1685_;
goto v___jp_1681_;
}
else
{
lean_object* v___f_1686_; lean_object* v___x_1687_; lean_object* v_path_1688_; lean_object* v___y_1690_; 
lean_inc(v___x_1680_);
v___f_1686_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1686_, 0, v___x_1680_);
v___x_1687_ = lean_box(0);
lean_inc(v_k_1676_);
v_path_1688_ = l_Lean_Level_Normalize_findParent(v___f_1686_, v___x_1687_, v_k_1676_);
if (lean_obj_tag(v_path_1688_) == 1)
{
lean_object* v_tail_1701_; 
v_tail_1701_ = lean_ctor_get(v_path_1688_, 1);
lean_inc(v_tail_1701_);
if (lean_obj_tag(v_tail_1701_) == 0)
{
lean_object* v_head_1702_; lean_object* v_var_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_head_1702_ = lean_ctor_get(v_path_1688_, 0);
lean_inc(v_head_1702_);
v_var_1703_ = lean_ctor_get(v_n_u2081_1685_, 2);
lean_inc(v_var_1703_);
v___x_1704_ = lean_unsigned_to_nat(0u);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_head_1702_);
lean_ctor_set(v___x_1705_, 1, v___x_1704_);
v___x_1706_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1706_, 0, v___x_1705_);
lean_ctor_set(v___x_1706_, 1, v___x_1687_);
v___x_1707_ = l_Lean_Level_Normalize_subsumeVars(v_var_1703_, v___x_1706_);
v___y_1690_ = v___x_1707_;
goto v___jp_1689_;
}
else
{
lean_object* v_var_1708_; 
lean_dec(v_tail_1701_);
v_var_1708_ = lean_ctor_get(v_n_u2081_1685_, 2);
lean_inc(v_var_1708_);
v___y_1690_ = v_var_1708_;
goto v___jp_1689_;
}
}
else
{
lean_object* v_var_1709_; 
v_var_1709_ = lean_ctor_get(v_n_u2081_1685_, 2);
lean_inc(v_var_1709_);
v___y_1690_ = v_var_1709_;
goto v___jp_1689_;
}
v___jp_1689_:
{
lean_object* v_const_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
v_const_1691_ = lean_ctor_get(v_n_u2081_1685_, 1);
v_isSharedCheck_1698_ = !lean_is_exclusive(v_n_u2081_1685_);
if (v_isSharedCheck_1698_ == 0)
{
lean_object* v_unused_1699_; lean_object* v_unused_1700_; 
v_unused_1699_ = lean_ctor_get(v_n_u2081_1685_, 2);
lean_dec(v_unused_1699_);
v_unused_1700_ = lean_ctor_get(v_n_u2081_1685_, 0);
lean_dec(v_unused_1700_);
v___x_1693_ = v_n_u2081_1685_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_const_1691_);
lean_dec(v_n_u2081_1685_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
lean_ctor_set(v___x_1693_, 2, v___y_1690_);
lean_ctor_set(v___x_1693_, 0, v_path_1688_);
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_path_1688_);
lean_ctor_set(v_reuseFailAlloc_1697_, 1, v_const_1691_);
lean_ctor_set(v_reuseFailAlloc_1697_, 2, v___y_1690_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
v___y_1682_ = v___x_1696_;
goto v___jp_1681_;
}
}
}
}
v___jp_1681_:
{
lean_object* v___x_1683_; 
v___x_1683_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1___redArg(v_k_1676_, v___y_1682_, v___x_1680_);
v_init_1674_ = v___x_1683_;
v_x_1675_ = v_r_1679_;
goto _start;
}
}
else
{
return v_init_1674_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5___boxed(lean_object* v_paths_1710_, lean_object* v_init_1711_, lean_object* v_x_1712_){
_start:
{
uint8_t v_paths_boxed_1713_; lean_object* v_res_1714_; 
v_paths_boxed_1713_ = lean_unbox(v_paths_1710_);
v_res_1714_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5(v_paths_boxed_1713_, v_init_1711_, v_x_1712_);
return v_res_1714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_subsumption(lean_object* v_acc_1715_, uint8_t v_paths_1716_){
_start:
{
lean_object* v___x_1717_; 
lean_inc(v_acc_1715_);
v___x_1717_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5(v_paths_1716_, v_acc_1715_, v_acc_1715_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_subsumption___boxed(lean_object* v_acc_1718_, lean_object* v_paths_1719_){
_start:
{
uint8_t v_paths_boxed_1720_; lean_object* v_res_1721_; 
v_paths_boxed_1720_ = lean_unbox(v_paths_1719_);
v_res_1721_ = l_Lean_Level_Normalize_NormLevel_subsumption(v_acc_1718_, v_paths_boxed_1720_);
return v_res_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1(lean_object* v_00_u03b2_1722_, lean_object* v_k_1723_, lean_object* v_v_1724_, lean_object* v_t_1725_, lean_object* v_hl_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1___redArg(v_k_1723_, v_v_1724_, v_t_1725_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__2(lean_object* v_p_u2081_1728_, lean_object* v_init_1729_, lean_object* v_t_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__2_spec__2(v_p_u2081_1728_, v_init_1729_, v_t_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3(lean_object* v_00_u03b2_1732_, lean_object* v_k_1733_, lean_object* v_t_1734_){
_start:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___redArg(v_k_1733_, v_t_1734_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3___boxed(lean_object* v_00_u03b2_1736_, lean_object* v_k_1737_, lean_object* v_t_1738_){
_start:
{
uint8_t v_res_1739_; lean_object* v_r_1740_; 
v_res_1739_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__3(v_00_u03b2_1736_, v_k_1737_, v_t_1738_);
lean_dec(v_t_1738_);
lean_dec(v_k_1737_);
v_r_1740_ = lean_box(v_res_1739_);
return v_r_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4(uint8_t v_paths_1741_, lean_object* v_init_1742_, lean_object* v_t_1743_){
_start:
{
lean_object* v___x_1744_; 
v___x_1744_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5(v_paths_1741_, v_init_1742_, v_t_1743_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4___boxed(lean_object* v_paths_1745_, lean_object* v_init_1746_, lean_object* v_t_1747_){
_start:
{
uint8_t v_paths_boxed_1748_; lean_object* v_res_1749_; 
v_paths_boxed_1748_ = lean_unbox(v_paths_1745_);
v_res_1749_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4(v_paths_boxed_1748_, v_init_1746_, v_t_1747_);
return v_res_1749_;
}
}
static lean_object* _init_l_Lean_Level_Normalize_normalize___closed__0(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = lean_box(1);
v___x_1751_ = ((lean_object*)(l_Lean_Level_Normalize_instInhabitedNode_default));
v___x_1752_ = lean_box(0);
v___x_1753_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__1___redArg(v___x_1752_, v___x_1751_, v___x_1750_);
return v___x_1753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_normalize(lean_object* v_l_1754_, uint8_t v_paths_1755_){
_start:
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; 
v___x_1756_ = lean_box(0);
v___x_1757_ = lean_unsigned_to_nat(0u);
v___x_1758_ = lean_obj_once(&l_Lean_Level_Normalize_normalize___closed__0, &l_Lean_Level_Normalize_normalize___closed__0_once, _init_l_Lean_Level_Normalize_normalize___closed__0);
v___x_1759_ = l_Lean_Level_Normalize_normalizeAux(v_l_1754_, v___x_1756_, v___x_1757_, v___x_1758_);
lean_inc(v___x_1759_);
v___x_1760_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_subsumption_spec__4_spec__5(v_paths_1755_, v___x_1759_, v___x_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_normalize___boxed(lean_object* v_l_1761_, lean_object* v_paths_1762_){
_start:
{
uint8_t v_paths_boxed_1763_; lean_object* v_res_1764_; 
v_paths_boxed_1763_ = lean_unbox(v_paths_1762_);
v_res_1764_ = l_Lean_Level_Normalize_normalize(v_l_1761_, v_paths_boxed_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_leVars(lean_object* v_x_1765_, lean_object* v_x_1766_){
_start:
{
if (lean_obj_tag(v_x_1765_) == 0)
{
uint8_t v___x_1767_; 
v___x_1767_ = 1;
return v___x_1767_;
}
else
{
if (lean_obj_tag(v_x_1766_) == 0)
{
uint8_t v___x_1768_; 
v___x_1768_ = 0;
return v___x_1768_;
}
else
{
lean_object* v_head_1769_; lean_object* v_head_1770_; lean_object* v_tail_1771_; lean_object* v_tail_1772_; lean_object* v_var_1773_; lean_object* v_offset_1774_; lean_object* v_var_1775_; lean_object* v_offset_1776_; uint8_t v___x_1777_; 
v_head_1769_ = lean_ctor_get(v_x_1765_, 0);
v_head_1770_ = lean_ctor_get(v_x_1766_, 0);
v_tail_1771_ = lean_ctor_get(v_x_1765_, 1);
v_tail_1772_ = lean_ctor_get(v_x_1766_, 1);
v_var_1773_ = lean_ctor_get(v_head_1769_, 0);
v_offset_1774_ = lean_ctor_get(v_head_1769_, 1);
v_var_1775_ = lean_ctor_get(v_head_1770_, 0);
v_offset_1776_ = lean_ctor_get(v_head_1770_, 1);
v___x_1777_ = l_Lean_Name_cmp(v_var_1773_, v_var_1775_);
switch(v___x_1777_)
{
case 0:
{
uint8_t v___x_1778_; 
v___x_1778_ = 0;
return v___x_1778_;
}
case 1:
{
uint8_t v___x_1779_; 
v___x_1779_ = lean_nat_dec_le(v_offset_1774_, v_offset_1776_);
if (v___x_1779_ == 0)
{
return v___x_1779_;
}
else
{
v_x_1765_ = v_tail_1771_;
v_x_1766_ = v_tail_1772_;
goto _start;
}
}
default: 
{
v_x_1766_ = v_tail_1772_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_leVars___boxed(lean_object* v_x_1782_, lean_object* v_x_1783_){
_start:
{
uint8_t v_res_1784_; lean_object* v_r_1785_; 
v_res_1784_ = l_Lean_Level_Normalize_leVars(v_x_1782_, v_x_1783_);
lean_dec(v_x_1783_);
lean_dec(v_x_1782_);
v_r_1785_ = lean_box(v_res_1784_);
return v_r_1785_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean_Level_Normalize_NormLevel_le_spec__0(lean_object* v___x_1786_, lean_object* v_x_1787_){
_start:
{
if (lean_obj_tag(v_x_1787_) == 0)
{
uint8_t v___x_1788_; 
v___x_1788_ = 0;
return v___x_1788_;
}
else
{
lean_object* v_head_1789_; lean_object* v_tail_1790_; lean_object* v_offset_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; uint8_t v___x_1794_; 
v_head_1789_ = lean_ctor_get(v_x_1787_, 0);
v_tail_1790_ = lean_ctor_get(v_x_1787_, 1);
v_offset_1791_ = lean_ctor_get(v_head_1789_, 1);
v___x_1792_ = lean_unsigned_to_nat(1u);
v___x_1793_ = lean_nat_add(v_offset_1791_, v___x_1792_);
v___x_1794_ = lean_nat_dec_le(v___x_1786_, v___x_1793_);
lean_dec(v___x_1793_);
if (v___x_1794_ == 0)
{
v_x_1787_ = v_tail_1790_;
goto _start;
}
else
{
return v___x_1794_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean_Level_Normalize_NormLevel_le_spec__0___boxed(lean_object* v___x_1796_, lean_object* v_x_1797_){
_start:
{
uint8_t v_res_1798_; lean_object* v_r_1799_; 
v_res_1798_ = l_List_any___at___00Lean_Level_Normalize_NormLevel_le_spec__0(v___x_1796_, v_x_1797_);
lean_dec(v_x_1797_);
lean_dec(v___x_1796_);
v_r_1799_ = lean_box(v_res_1798_);
return v_r_1799_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(lean_object* v_b_1800_, lean_object* v_a_1801_, lean_object* v___x_1802_, lean_object* v_init_1803_, lean_object* v_x_1804_){
_start:
{
if (lean_obj_tag(v_x_1804_) == 0)
{
lean_object* v_k_1805_; lean_object* v_v_1806_; lean_object* v_l_1807_; lean_object* v_r_1808_; lean_object* v___x_1809_; 
v_k_1805_ = lean_ctor_get(v_x_1804_, 1);
lean_inc(v_k_1805_);
v_v_1806_ = lean_ctor_get(v_x_1804_, 2);
lean_inc(v_v_1806_);
v_l_1807_ = lean_ctor_get(v_x_1804_, 3);
lean_inc(v_l_1807_);
v_r_1808_ = lean_ctor_get(v_x_1804_, 4);
lean_inc(v_r_1808_);
lean_dec_ref(v_x_1804_);
lean_inc(v_a_1801_);
v___x_1809_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(v_b_1800_, v_a_1801_, v___x_1802_, v_init_1803_, v_l_1807_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_dec(v_r_1808_);
lean_dec(v_v_1806_);
lean_dec(v_k_1805_);
lean_dec(v_a_1801_);
return v___x_1809_;
}
else
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1838_; 
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1838_ == 0)
{
lean_object* v_unused_1839_; 
v_unused_1839_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1839_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1838_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v_const_1813_; lean_object* v_var_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; uint8_t v___x_1834_; 
v_const_1813_ = lean_ctor_get(v_v_1806_, 1);
lean_inc(v_const_1813_);
v_var_1814_ = lean_ctor_get(v_v_1806_, 2);
lean_inc(v_var_1814_);
lean_dec(v_v_1806_);
v___x_1815_ = lean_box(0);
v___x_1816_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___x_1834_ = l_List_isEmpty___redArg(v_var_1814_);
if (v___x_1834_ == 0)
{
goto v___jp_1827_;
}
else
{
lean_object* v_var_1835_; uint8_t v___x_1836_; 
v_var_1835_ = lean_ctor_get(v_b_1800_, 2);
v___x_1836_ = l_List_isEmpty___redArg(v_var_1835_);
if (v___x_1836_ == 0)
{
lean_dec(v_var_1814_);
lean_dec(v_const_1813_);
lean_del_object(v___x_1811_);
lean_dec(v_k_1805_);
v_init_1803_ = v___x_1816_;
v_x_1804_ = v_r_1808_;
goto _start;
}
else
{
goto v___jp_1827_;
}
}
v___jp_1817_:
{
lean_object* v_var_1818_; uint8_t v___x_1819_; 
v_var_1818_ = lean_ctor_get(v_b_1800_, 2);
v___x_1819_ = l_Lean_Level_Normalize_leVars(v_var_1818_, v_var_1814_);
lean_dec(v_var_1814_);
if (v___x_1819_ == 0)
{
lean_del_object(v___x_1811_);
v_init_1803_ = v___x_1816_;
v_x_1804_ = v_r_1808_;
goto _start;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1825_; 
lean_dec(v_r_1808_);
lean_dec(v_a_1801_);
v___x_1821_ = lean_box(v___x_1819_);
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
v___x_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1823_, 0, v___x_1822_);
lean_ctor_set(v___x_1823_, 1, v___x_1815_);
if (v_isShared_1812_ == 0)
{
lean_ctor_set_tag(v___x_1811_, 0);
lean_ctor_set(v___x_1811_, 0, v___x_1823_);
v___x_1825_ = v___x_1811_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
v___x_1825_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
return v___x_1825_;
}
}
}
v___jp_1827_:
{
lean_object* v___x_1828_; uint8_t v___x_1829_; 
v___x_1828_ = ((lean_object*)(l_Lean_Level_Normalize_instOrdName___closed__0));
lean_inc(v_a_1801_);
v___x_1829_ = l_Lean_Level_Normalize_subset___redArg(v___x_1828_, v_k_1805_, v_a_1801_);
if (v___x_1829_ == 0)
{
lean_dec(v_var_1814_);
lean_dec(v_const_1813_);
lean_del_object(v___x_1811_);
v_init_1803_ = v___x_1816_;
v_x_1804_ = v_r_1808_;
goto _start;
}
else
{
uint8_t v___x_1831_; 
v___x_1831_ = lean_nat_dec_le(v___x_1802_, v_const_1813_);
lean_dec(v_const_1813_);
if (v___x_1831_ == 0)
{
uint8_t v___x_1832_; 
v___x_1832_ = l_List_any___at___00Lean_Level_Normalize_NormLevel_le_spec__0(v___x_1802_, v_var_1814_);
if (v___x_1832_ == 0)
{
lean_dec(v_var_1814_);
lean_del_object(v___x_1811_);
v_init_1803_ = v___x_1816_;
v_x_1804_ = v_r_1808_;
goto _start;
}
else
{
goto v___jp_1817_;
}
}
else
{
goto v___jp_1817_;
}
}
}
}
}
}
else
{
lean_object* v___x_1840_; 
lean_dec(v_a_1801_);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_init_1803_);
return v___x_1840_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1___boxed(lean_object* v_b_1841_, lean_object* v_a_1842_, lean_object* v___x_1843_, lean_object* v_init_1844_, lean_object* v_x_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(v_b_1841_, v_a_1842_, v___x_1843_, v_init_1844_, v_x_1845_);
lean_dec(v___x_1843_);
lean_dec_ref(v_b_1841_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1(lean_object* v_b_1847_, lean_object* v_a_1848_, lean_object* v___x_1849_, lean_object* v_init_1850_, lean_object* v_x_1851_){
_start:
{
if (lean_obj_tag(v_x_1851_) == 0)
{
lean_object* v_k_1852_; lean_object* v_v_1853_; lean_object* v_l_1854_; lean_object* v_r_1855_; lean_object* v___x_1856_; 
v_k_1852_ = lean_ctor_get(v_x_1851_, 1);
lean_inc(v_k_1852_);
v_v_1853_ = lean_ctor_get(v_x_1851_, 2);
lean_inc(v_v_1853_);
v_l_1854_ = lean_ctor_get(v_x_1851_, 3);
lean_inc(v_l_1854_);
v_r_1855_ = lean_ctor_get(v_x_1851_, 4);
lean_inc(v_r_1855_);
lean_dec_ref(v_x_1851_);
lean_inc(v_a_1848_);
v___x_1856_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(v_b_1847_, v_a_1848_, v___x_1849_, v_init_1850_, v_l_1854_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_dec(v_r_1855_);
lean_dec(v_v_1853_);
lean_dec(v_k_1852_);
lean_dec(v_a_1848_);
return v___x_1856_;
}
else
{
lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1885_; 
v_isSharedCheck_1885_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1885_ == 0)
{
lean_object* v_unused_1886_; 
v_unused_1886_ = lean_ctor_get(v___x_1856_, 0);
lean_dec(v_unused_1886_);
v___x_1858_ = v___x_1856_;
v_isShared_1859_ = v_isSharedCheck_1885_;
goto v_resetjp_1857_;
}
else
{
lean_dec(v___x_1856_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1885_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_const_1860_; lean_object* v_var_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; uint8_t v___x_1881_; 
v_const_1860_ = lean_ctor_get(v_v_1853_, 1);
lean_inc(v_const_1860_);
v_var_1861_ = lean_ctor_get(v_v_1853_, 2);
lean_inc(v_var_1861_);
lean_dec(v_v_1853_);
v___x_1862_ = lean_box(0);
v___x_1863_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___x_1881_ = l_List_isEmpty___redArg(v_var_1861_);
if (v___x_1881_ == 0)
{
goto v___jp_1874_;
}
else
{
lean_object* v_var_1882_; uint8_t v___x_1883_; 
v_var_1882_ = lean_ctor_get(v_b_1847_, 2);
v___x_1883_ = l_List_isEmpty___redArg(v_var_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; 
lean_dec(v_var_1861_);
lean_dec(v_const_1860_);
lean_del_object(v___x_1858_);
lean_dec(v_k_1852_);
v___x_1884_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(v_b_1847_, v_a_1848_, v___x_1849_, v___x_1863_, v_r_1855_);
return v___x_1884_;
}
else
{
goto v___jp_1874_;
}
}
v___jp_1864_:
{
lean_object* v_var_1865_; uint8_t v___x_1866_; 
v_var_1865_ = lean_ctor_get(v_b_1847_, 2);
v___x_1866_ = l_Lean_Level_Normalize_leVars(v_var_1865_, v_var_1861_);
lean_dec(v_var_1861_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1867_; 
lean_del_object(v___x_1858_);
v___x_1867_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(v_b_1847_, v_a_1848_, v___x_1849_, v___x_1863_, v_r_1855_);
return v___x_1867_;
}
else
{
lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1872_; 
lean_dec(v_r_1855_);
lean_dec(v_a_1848_);
v___x_1868_ = lean_box(v___x_1866_);
v___x_1869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
lean_ctor_set(v___x_1870_, 1, v___x_1862_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set_tag(v___x_1858_, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1870_);
v___x_1872_ = v___x_1858_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v___x_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
v___jp_1874_:
{
lean_object* v___x_1875_; uint8_t v___x_1876_; 
v___x_1875_ = ((lean_object*)(l_Lean_Level_Normalize_instOrdName___closed__0));
lean_inc(v_a_1848_);
v___x_1876_ = l_Lean_Level_Normalize_subset___redArg(v___x_1875_, v_k_1852_, v_a_1848_);
if (v___x_1876_ == 0)
{
lean_object* v___x_1877_; 
lean_dec(v_var_1861_);
lean_dec(v_const_1860_);
lean_del_object(v___x_1858_);
v___x_1877_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(v_b_1847_, v_a_1848_, v___x_1849_, v___x_1863_, v_r_1855_);
return v___x_1877_;
}
else
{
uint8_t v___x_1878_; 
v___x_1878_ = lean_nat_dec_le(v___x_1849_, v_const_1860_);
lean_dec(v_const_1860_);
if (v___x_1878_ == 0)
{
uint8_t v___x_1879_; 
v___x_1879_ = l_List_any___at___00Lean_Level_Normalize_NormLevel_le_spec__0(v___x_1849_, v_var_1861_);
if (v___x_1879_ == 0)
{
lean_object* v___x_1880_; 
lean_dec(v_var_1861_);
lean_del_object(v___x_1858_);
v___x_1880_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1_spec__1(v_b_1847_, v_a_1848_, v___x_1849_, v___x_1863_, v_r_1855_);
return v___x_1880_;
}
else
{
goto v___jp_1864_;
}
}
else
{
goto v___jp_1864_;
}
}
}
}
}
}
else
{
lean_object* v___x_1887_; 
lean_dec(v_a_1848_);
v___x_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1887_, 0, v_init_1850_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1___boxed(lean_object* v_b_1888_, lean_object* v_a_1889_, lean_object* v___x_1890_, lean_object* v_init_1891_, lean_object* v_x_1892_){
_start:
{
lean_object* v_res_1893_; 
v_res_1893_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1(v_b_1888_, v_a_1889_, v___x_1890_, v_init_1891_, v_x_1892_);
lean_dec(v___x_1890_);
lean_dec_ref(v_b_1888_);
return v_res_1893_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2_spec__3(lean_object* v_l_u2082_1894_, lean_object* v_init_1895_, lean_object* v_x_1896_){
_start:
{
if (lean_obj_tag(v_x_1896_) == 0)
{
lean_object* v_k_1897_; lean_object* v_v_1898_; lean_object* v_l_1899_; lean_object* v_r_1900_; lean_object* v___x_1901_; 
v_k_1897_ = lean_ctor_get(v_x_1896_, 1);
lean_inc(v_k_1897_);
v_v_1898_ = lean_ctor_get(v_x_1896_, 2);
lean_inc(v_v_1898_);
v_l_1899_ = lean_ctor_get(v_x_1896_, 3);
lean_inc(v_l_1899_);
v_r_1900_ = lean_ctor_get(v_x_1896_, 4);
lean_inc(v_r_1900_);
lean_dec_ref(v_x_1896_);
lean_inc(v_l_u2082_1894_);
v___x_1901_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2_spec__3(v_l_u2082_1894_, v_init_1895_, v_l_1899_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_dec(v_r_1900_);
lean_dec(v_v_1898_);
lean_dec(v_k_1897_);
lean_dec(v_l_u2082_1894_);
return v___x_1901_;
}
else
{
lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1933_; 
v_isSharedCheck_1933_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1933_ == 0)
{
lean_object* v_unused_1934_; 
v_unused_1934_ = lean_ctor_get(v___x_1901_, 0);
lean_dec(v_unused_1934_);
v___x_1903_ = v___x_1901_;
v_isShared_1904_ = v_isSharedCheck_1933_;
goto v_resetjp_1902_;
}
else
{
lean_dec(v___x_1901_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1933_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v_const_1905_; lean_object* v_var_1906_; lean_object* v___x_1907_; uint8_t v___y_1909_; lean_object* v___x_1916_; uint8_t v___y_1918_; lean_object* v___y_1919_; uint8_t v___y_1926_; lean_object* v___x_1930_; uint8_t v___x_1931_; 
v_const_1905_ = lean_ctor_get(v_v_1898_, 1);
lean_inc(v_const_1905_);
v_var_1906_ = lean_ctor_get(v_v_1898_, 2);
v___x_1907_ = lean_box(0);
v___x_1916_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___x_1930_ = lean_unsigned_to_nat(0u);
v___x_1931_ = lean_nat_dec_eq(v_const_1905_, v___x_1930_);
if (v___x_1931_ == 0)
{
v___y_1926_ = v___x_1931_;
goto v___jp_1925_;
}
else
{
uint8_t v___x_1932_; 
v___x_1932_ = l_List_isEmpty___redArg(v_var_1906_);
v___y_1926_ = v___x_1932_;
goto v___jp_1925_;
}
v___jp_1908_:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1914_; 
v___x_1910_ = lean_box(v___y_1909_);
v___x_1911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
v___x_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
lean_ctor_set(v___x_1912_, 1, v___x_1907_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 0);
lean_ctor_set(v___x_1903_, 0, v___x_1912_);
v___x_1914_ = v___x_1903_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v___x_1912_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
return v___x_1914_;
}
}
v___jp_1917_:
{
lean_object* v_fst_1920_; 
v_fst_1920_ = lean_ctor_get(v___y_1919_, 0);
lean_inc(v_fst_1920_);
lean_dec_ref(v___y_1919_);
if (lean_obj_tag(v_fst_1920_) == 0)
{
lean_dec(v_r_1900_);
lean_dec(v_l_u2082_1894_);
v___y_1909_ = v___y_1918_;
goto v___jp_1908_;
}
else
{
lean_object* v_val_1921_; uint8_t v___x_1922_; 
v_val_1921_ = lean_ctor_get(v_fst_1920_, 0);
lean_inc(v_val_1921_);
lean_dec_ref(v_fst_1920_);
v___x_1922_ = lean_unbox(v_val_1921_);
if (v___x_1922_ == 0)
{
uint8_t v___x_1923_; 
lean_dec(v_r_1900_);
lean_dec(v_l_u2082_1894_);
v___x_1923_ = lean_unbox(v_val_1921_);
lean_dec(v_val_1921_);
v___y_1909_ = v___x_1923_;
goto v___jp_1908_;
}
else
{
lean_dec(v_val_1921_);
lean_del_object(v___x_1903_);
v_init_1895_ = v___x_1916_;
v_x_1896_ = v_r_1900_;
goto _start;
}
}
}
v___jp_1925_:
{
if (v___y_1926_ == 0)
{
lean_object* v___x_1927_; lean_object* v_a_1928_; 
lean_inc(v_l_u2082_1894_);
v___x_1927_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1(v_v_1898_, v_k_1897_, v_const_1905_, v___x_1916_, v_l_u2082_1894_);
lean_dec(v_const_1905_);
lean_dec(v_v_1898_);
v_a_1928_ = lean_ctor_get(v___x_1927_, 0);
lean_inc(v_a_1928_);
lean_dec_ref(v___x_1927_);
v___y_1918_ = v___y_1926_;
v___y_1919_ = v_a_1928_;
goto v___jp_1917_;
}
else
{
lean_dec(v_const_1905_);
lean_del_object(v___x_1903_);
lean_dec(v_v_1898_);
lean_dec(v_k_1897_);
v_init_1895_ = v___x_1916_;
v_x_1896_ = v_r_1900_;
goto _start;
}
}
}
}
}
else
{
lean_object* v___x_1935_; 
lean_dec(v_l_u2082_1894_);
v___x_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_init_1895_);
return v___x_1935_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2(lean_object* v_l_u2082_1936_, lean_object* v_init_1937_, lean_object* v_x_1938_){
_start:
{
if (lean_obj_tag(v_x_1938_) == 0)
{
lean_object* v_k_1939_; lean_object* v_v_1940_; lean_object* v_l_1941_; lean_object* v_r_1942_; lean_object* v___x_1943_; 
v_k_1939_ = lean_ctor_get(v_x_1938_, 1);
lean_inc(v_k_1939_);
v_v_1940_ = lean_ctor_get(v_x_1938_, 2);
lean_inc(v_v_1940_);
v_l_1941_ = lean_ctor_get(v_x_1938_, 3);
lean_inc(v_l_1941_);
v_r_1942_ = lean_ctor_get(v_x_1938_, 4);
lean_inc(v_r_1942_);
lean_dec_ref(v_x_1938_);
lean_inc(v_l_u2082_1936_);
v___x_1943_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2_spec__3(v_l_u2082_1936_, v_init_1937_, v_l_1941_);
if (lean_obj_tag(v___x_1943_) == 0)
{
lean_dec(v_r_1942_);
lean_dec(v_v_1940_);
lean_dec(v_k_1939_);
lean_dec(v_l_u2082_1936_);
return v___x_1943_;
}
else
{
lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_1975_; 
v_isSharedCheck_1975_ = !lean_is_exclusive(v___x_1943_);
if (v_isSharedCheck_1975_ == 0)
{
lean_object* v_unused_1976_; 
v_unused_1976_ = lean_ctor_get(v___x_1943_, 0);
lean_dec(v_unused_1976_);
v___x_1945_ = v___x_1943_;
v_isShared_1946_ = v_isSharedCheck_1975_;
goto v_resetjp_1944_;
}
else
{
lean_dec(v___x_1943_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_1975_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v_const_1947_; lean_object* v_var_1948_; lean_object* v___x_1949_; uint8_t v___y_1951_; lean_object* v___x_1958_; uint8_t v___y_1960_; lean_object* v___y_1961_; uint8_t v___y_1968_; lean_object* v___x_1972_; uint8_t v___x_1973_; 
v_const_1947_ = lean_ctor_get(v_v_1940_, 1);
lean_inc(v_const_1947_);
v_var_1948_ = lean_ctor_get(v_v_1940_, 2);
v___x_1949_ = lean_box(0);
v___x_1958_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___x_1972_ = lean_unsigned_to_nat(0u);
v___x_1973_ = lean_nat_dec_eq(v_const_1947_, v___x_1972_);
if (v___x_1973_ == 0)
{
v___y_1968_ = v___x_1973_;
goto v___jp_1967_;
}
else
{
uint8_t v___x_1974_; 
v___x_1974_ = l_List_isEmpty___redArg(v_var_1948_);
v___y_1968_ = v___x_1974_;
goto v___jp_1967_;
}
v___jp_1950_:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; 
v___x_1952_ = lean_box(v___y_1951_);
v___x_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1953_, 0, v___x_1952_);
v___x_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1954_, 0, v___x_1953_);
lean_ctor_set(v___x_1954_, 1, v___x_1949_);
if (v_isShared_1946_ == 0)
{
lean_ctor_set_tag(v___x_1945_, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1954_);
v___x_1956_ = v___x_1945_;
goto v_reusejp_1955_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v___x_1954_);
v___x_1956_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1955_;
}
v_reusejp_1955_:
{
return v___x_1956_;
}
}
v___jp_1959_:
{
lean_object* v_fst_1962_; 
v_fst_1962_ = lean_ctor_get(v___y_1961_, 0);
lean_inc(v_fst_1962_);
lean_dec_ref(v___y_1961_);
if (lean_obj_tag(v_fst_1962_) == 0)
{
lean_dec(v_r_1942_);
lean_dec(v_l_u2082_1936_);
v___y_1951_ = v___y_1960_;
goto v___jp_1950_;
}
else
{
lean_object* v_val_1963_; uint8_t v___x_1964_; 
v_val_1963_ = lean_ctor_get(v_fst_1962_, 0);
lean_inc(v_val_1963_);
lean_dec_ref(v_fst_1962_);
v___x_1964_ = lean_unbox(v_val_1963_);
if (v___x_1964_ == 0)
{
uint8_t v___x_1965_; 
lean_dec(v_r_1942_);
lean_dec(v_l_u2082_1936_);
v___x_1965_ = lean_unbox(v_val_1963_);
lean_dec(v_val_1963_);
v___y_1951_ = v___x_1965_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_1966_; 
lean_dec(v_val_1963_);
lean_del_object(v___x_1945_);
v___x_1966_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2_spec__3(v_l_u2082_1936_, v___x_1958_, v_r_1942_);
return v___x_1966_;
}
}
}
v___jp_1967_:
{
if (v___y_1968_ == 0)
{
lean_object* v___x_1969_; lean_object* v_a_1970_; 
lean_inc(v_l_u2082_1936_);
v___x_1969_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__1(v_v_1940_, v_k_1939_, v_const_1947_, v___x_1958_, v_l_u2082_1936_);
lean_dec(v_const_1947_);
lean_dec(v_v_1940_);
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref(v___x_1969_);
v___y_1960_ = v___y_1968_;
v___y_1961_ = v_a_1970_;
goto v___jp_1959_;
}
else
{
lean_object* v___x_1971_; 
lean_dec(v_const_1947_);
lean_del_object(v___x_1945_);
lean_dec(v_v_1940_);
lean_dec(v_k_1939_);
v___x_1971_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2_spec__3(v_l_u2082_1936_, v___x_1958_, v_r_1942_);
return v___x_1971_;
}
}
}
}
}
else
{
lean_object* v___x_1977_; 
lean_dec(v_l_u2082_1936_);
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_init_1937_);
return v___x_1977_;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Level_Normalize_NormLevel_le(lean_object* v_l_u2081_1978_, lean_object* v_l_u2082_1979_){
_start:
{
lean_object* v___y_1981_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v_a_1988_; 
v___x_1986_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___x_1987_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_Normalize_NormLevel_le_spec__2(v_l_u2082_1979_, v___x_1986_, v_l_u2081_1978_);
v_a_1988_ = lean_ctor_get(v___x_1987_, 0);
lean_inc(v_a_1988_);
lean_dec_ref(v___x_1987_);
v___y_1981_ = v_a_1988_;
goto v___jp_1980_;
v___jp_1980_:
{
lean_object* v_fst_1982_; 
v_fst_1982_ = lean_ctor_get(v___y_1981_, 0);
lean_inc(v_fst_1982_);
lean_dec_ref(v___y_1981_);
if (lean_obj_tag(v_fst_1982_) == 0)
{
uint8_t v___x_1983_; 
v___x_1983_ = 1;
return v___x_1983_;
}
else
{
lean_object* v_val_1984_; uint8_t v___x_1985_; 
v_val_1984_ = lean_ctor_get(v_fst_1982_, 0);
lean_inc(v_val_1984_);
lean_dec_ref(v_fst_1982_);
v___x_1985_ = lean_unbox(v_val_1984_);
lean_dec(v_val_1984_);
return v___x_1985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_le___boxed(lean_object* v_l_u2081_1989_, lean_object* v_l_u2082_1990_){
_start:
{
uint8_t v_res_1991_; lean_object* v_r_1992_; 
v_res_1991_ = l_Lean_Level_Normalize_NormLevel_le(v_l_u2081_1989_, v_l_u2082_1990_);
v_r_1992_ = lean_box(v_res_1991_);
return v_r_1992_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_buildPaths_setPath_spec__0(lean_object* v_path_1993_, lean_object* v_k_1994_, lean_object* v_t_1995_){
_start:
{
if (lean_obj_tag(v_t_1995_) == 0)
{
lean_object* v_size_1996_; lean_object* v_k_1997_; lean_object* v_v_1998_; lean_object* v_l_1999_; lean_object* v_r_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2026_; 
v_size_1996_ = lean_ctor_get(v_t_1995_, 0);
v_k_1997_ = lean_ctor_get(v_t_1995_, 1);
v_v_1998_ = lean_ctor_get(v_t_1995_, 2);
v_l_1999_ = lean_ctor_get(v_t_1995_, 3);
v_r_2000_ = lean_ctor_get(v_t_1995_, 4);
v_isSharedCheck_2026_ = !lean_is_exclusive(v_t_1995_);
if (v_isSharedCheck_2026_ == 0)
{
v___x_2002_ = v_t_1995_;
v_isShared_2003_ = v_isSharedCheck_2026_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_r_2000_);
lean_inc(v_l_1999_);
lean_inc(v_v_1998_);
lean_inc(v_k_1997_);
lean_inc(v_size_1996_);
lean_dec(v_t_1995_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2026_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
uint8_t v___x_2004_; 
v___x_2004_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_1994_, v_k_1997_);
switch(v___x_2004_)
{
case 0:
{
lean_object* v___x_2005_; lean_object* v___x_2007_; 
v___x_2005_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_buildPaths_setPath_spec__0(v_path_1993_, v_k_1994_, v_l_1999_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 3, v___x_2005_);
v___x_2007_ = v___x_2002_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_size_1996_);
lean_ctor_set(v_reuseFailAlloc_2008_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2008_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2008_, 3, v___x_2005_);
lean_ctor_set(v_reuseFailAlloc_2008_, 4, v_r_2000_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
case 1:
{
lean_object* v_const_2009_; lean_object* v_var_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2020_; 
lean_dec(v_k_1997_);
v_const_2009_ = lean_ctor_get(v_v_1998_, 1);
v_var_2010_ = lean_ctor_get(v_v_1998_, 2);
v_isSharedCheck_2020_ = !lean_is_exclusive(v_v_1998_);
if (v_isSharedCheck_2020_ == 0)
{
lean_object* v_unused_2021_; 
v_unused_2021_ = lean_ctor_get(v_v_1998_, 0);
lean_dec(v_unused_2021_);
v___x_2012_ = v_v_1998_;
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_var_2010_);
lean_inc(v_const_2009_);
lean_dec(v_v_1998_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2020_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 0, v_path_1993_);
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_path_1993_);
lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_const_2009_);
lean_ctor_set(v_reuseFailAlloc_2019_, 2, v_var_2010_);
v___x_2015_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
lean_object* v___x_2017_; 
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 2, v___x_2015_);
lean_ctor_set(v___x_2002_, 1, v_k_1994_);
v___x_2017_ = v___x_2002_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_size_1996_);
lean_ctor_set(v_reuseFailAlloc_2018_, 1, v_k_1994_);
lean_ctor_set(v_reuseFailAlloc_2018_, 2, v___x_2015_);
lean_ctor_set(v_reuseFailAlloc_2018_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2018_, 4, v_r_2000_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
default: 
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_buildPaths_setPath_spec__0(v_path_1993_, v_k_1994_, v_r_2000_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 4, v___x_2022_);
v___x_2024_ = v___x_2002_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_size_1996_);
lean_ctor_set(v_reuseFailAlloc_2025_, 1, v_k_1997_);
lean_ctor_set(v_reuseFailAlloc_2025_, 2, v_v_1998_);
lean_ctor_set(v_reuseFailAlloc_2025_, 3, v_l_1999_);
lean_ctor_set(v_reuseFailAlloc_2025_, 4, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
return v___x_2024_;
}
}
}
}
}
else
{
lean_dec(v_k_1994_);
lean_dec(v_path_1993_);
return v_t_1995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths_setPath(lean_object* v_p_2027_, lean_object* v_path_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2030_ = lean_box(0);
v___x_2031_ = l_Std_DTreeMap_Internal_Impl_Const_modify___at___00Lean_Level_Normalize_NormLevel_buildPaths_setPath_spec__0(v_path_2028_, v_p_2027_, v_a_2029_);
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2030_);
lean_ctor_set(v___x_2032_, 1, v___x_2031_);
return v___x_2032_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0_spec__0(lean_object* v_msg_2033_){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = ((lean_object*)(l_Lean_Level_Normalize_instInhabitedNode_default));
v___x_2035_ = lean_panic_fn_borrowed(v___x_2034_, v_msg_2033_);
return v___x_2035_;
}
}
static lean_object* _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__3(void){
_start:
{
lean_object* v___x_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2039_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__2));
v___x_2040_ = lean_unsigned_to_nat(13u);
v___x_2041_ = lean_unsigned_to_nat(227u);
v___x_2042_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__1));
v___x_2043_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__0));
v___x_2044_ = l_mkPanicMessageWithDecl(v___x_2043_, v___x_2042_, v___x_2041_, v___x_2040_, v___x_2039_);
return v___x_2044_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0(lean_object* v_t_2045_, lean_object* v_k_2046_){
_start:
{
if (lean_obj_tag(v_t_2045_) == 0)
{
lean_object* v_k_2047_; lean_object* v_v_2048_; lean_object* v_l_2049_; lean_object* v_r_2050_; uint8_t v___x_2051_; 
v_k_2047_ = lean_ctor_get(v_t_2045_, 1);
v_v_2048_ = lean_ctor_get(v_t_2045_, 2);
v_l_2049_ = lean_ctor_get(v_t_2045_, 3);
v_r_2050_ = lean_ctor_get(v_t_2045_, 4);
v___x_2051_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_2046_, v_k_2047_);
switch(v___x_2051_)
{
case 0:
{
v_t_2045_ = v_l_2049_;
goto _start;
}
case 1:
{
lean_inc(v_v_2048_);
return v_v_2048_;
}
default: 
{
v_t_2045_ = v_r_2050_;
goto _start;
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2054_ = lean_obj_once(&l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__3, &l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__3_once, _init_l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___closed__3);
v___x_2055_ = l_panic___at___00Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0_spec__0(v___x_2054_);
return v___x_2055_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0___boxed(lean_object* v_t_2056_, lean_object* v_k_2057_){
_start:
{
lean_object* v_res_2058_; 
v_res_2058_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0(v_t_2056_, v_k_2057_);
lean_dec(v_k_2057_);
lean_dec(v_t_2056_);
return v_res_2058_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1_spec__2(lean_object* v_as_2059_, size_t v_i_2060_, size_t v_stop_2061_, lean_object* v_b_2062_){
_start:
{
uint8_t v___x_2063_; 
v___x_2063_ = lean_usize_dec_eq(v_i_2060_, v_stop_2061_);
if (v___x_2063_ == 0)
{
size_t v___x_2064_; size_t v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2064_ = ((size_t)1ULL);
v___x_2065_ = lean_usize_sub(v_i_2060_, v___x_2064_);
v___x_2066_ = lean_array_uget_borrowed(v_as_2059_, v___x_2065_);
lean_inc(v___x_2066_);
v___x_2067_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2067_, 0, v___x_2066_);
lean_ctor_set(v___x_2067_, 1, v_b_2062_);
v_i_2060_ = v___x_2065_;
v_b_2062_ = v___x_2067_;
goto _start;
}
else
{
return v_b_2062_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1_spec__2___boxed(lean_object* v_as_2069_, lean_object* v_i_2070_, lean_object* v_stop_2071_, lean_object* v_b_2072_){
_start:
{
size_t v_i_boxed_2073_; size_t v_stop_boxed_2074_; lean_object* v_res_2075_; 
v_i_boxed_2073_ = lean_unbox_usize(v_i_2070_);
lean_dec(v_i_2070_);
v_stop_boxed_2074_ = lean_unbox_usize(v_stop_2071_);
lean_dec(v_stop_2071_);
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1_spec__2(v_as_2069_, v_i_boxed_2073_, v_stop_boxed_2074_, v_b_2072_);
lean_dec_ref(v_as_2069_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1(lean_object* v_l_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_){
_start:
{
if (lean_obj_tag(v_a_2078_) == 0)
{
lean_dec_ref(v_a_2079_);
lean_inc(v_l_2076_);
return v_l_2076_;
}
else
{
lean_object* v_head_2080_; lean_object* v_tail_2081_; uint8_t v___x_2082_; 
v_head_2080_ = lean_ctor_get(v_a_2078_, 0);
lean_inc(v_head_2080_);
v_tail_2081_ = lean_ctor_get(v_a_2078_, 1);
lean_inc(v_tail_2081_);
lean_dec_ref(v_a_2078_);
v___x_2082_ = lean_name_eq(v_head_2080_, v_a_2077_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
v___x_2083_ = lean_array_push(v_a_2079_, v_head_2080_);
v_a_2078_ = v_tail_2081_;
v_a_2079_ = v___x_2083_;
goto _start;
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
lean_dec(v_head_2080_);
v___x_2085_ = lean_array_get_size(v_a_2079_);
v___x_2086_ = lean_unsigned_to_nat(0u);
v___x_2087_ = lean_nat_dec_lt(v___x_2086_, v___x_2085_);
if (v___x_2087_ == 0)
{
lean_dec_ref(v_a_2079_);
return v_tail_2081_;
}
else
{
size_t v___x_2088_; size_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2088_ = lean_usize_of_nat(v___x_2085_);
v___x_2089_ = ((size_t)0ULL);
v___x_2090_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1_spec__2(v_a_2079_, v___x_2088_, v___x_2089_, v_tail_2081_);
lean_dec_ref(v_a_2079_);
return v___x_2090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1___boxed(lean_object* v_l_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_){
_start:
{
lean_object* v_res_2095_; 
v_res_2095_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1(v_l_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
lean_dec(v_a_2092_);
lean_dec(v_l_2091_);
return v_res_2095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths_getPath(lean_object* v_p_2098_, lean_object* v_depth_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___y_2103_; lean_object* v_path_2106_; 
v___x_2101_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0(v_a_2100_, v_p_2098_);
v_path_2106_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_path_2106_);
if (lean_obj_tag(v_path_2106_) == 1)
{
lean_object* v_tail_2107_; 
v_tail_2107_ = lean_ctor_get(v_path_2106_, 1);
if (lean_obj_tag(v_tail_2107_) == 0)
{
lean_object* v_head_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2134_; 
v_head_2108_ = lean_ctor_get(v_path_2106_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v_path_2106_);
if (v_isSharedCheck_2134_ == 0)
{
lean_object* v_unused_2135_; 
v_unused_2135_ = lean_ctor_get(v_path_2106_, 1);
lean_dec(v_unused_2135_);
v___x_2110_ = v_path_2106_;
v_isShared_2111_ = v_isSharedCheck_2134_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_head_2108_);
lean_dec(v_path_2106_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2134_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v_zero_2112_; uint8_t v_isZero_2113_; 
v_zero_2112_ = lean_unsigned_to_nat(0u);
v_isZero_2113_ = lean_nat_dec_eq(v_depth_2099_, v_zero_2112_);
if (v_isZero_2113_ == 0)
{
lean_object* v_one_2114_; lean_object* v_n_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_fst_2119_; lean_object* v_snd_2120_; lean_object* v___x_2122_; 
lean_dec_ref(v___x_2101_);
v_one_2114_ = lean_unsigned_to_nat(1u);
v_n_2115_ = lean_nat_sub(v_depth_2099_, v_one_2114_);
v___x_2116_ = ((lean_object*)(l_Lean_Level_Normalize_NormLevel_buildPaths_getPath___closed__0));
lean_inc(v_p_2098_);
v___x_2117_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1(v_p_2098_, v_head_2108_, v_p_2098_, v___x_2116_);
v___x_2118_ = l_Lean_Level_Normalize_NormLevel_buildPaths_getPath(v___x_2117_, v_n_2115_, v_a_2100_);
lean_dec(v_n_2115_);
v_fst_2119_ = lean_ctor_get(v___x_2118_, 0);
lean_inc(v_fst_2119_);
v_snd_2120_ = lean_ctor_get(v___x_2118_, 1);
lean_inc(v_snd_2120_);
lean_dec_ref(v___x_2118_);
if (v_isShared_2111_ == 0)
{
lean_ctor_set(v___x_2110_, 1, v_fst_2119_);
v___x_2122_ = v___x_2110_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_head_2108_);
lean_ctor_set(v_reuseFailAlloc_2133_, 1, v_fst_2119_);
v___x_2122_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2123_; lean_object* v_snd_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_inc_ref(v___x_2122_);
v___x_2123_ = l_Lean_Level_Normalize_NormLevel_buildPaths_setPath(v_p_2098_, v___x_2122_, v_snd_2120_);
v_snd_2124_ = lean_ctor_get(v___x_2123_, 1);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2131_ == 0)
{
lean_object* v_unused_2132_; 
v_unused_2132_ = lean_ctor_get(v___x_2123_, 0);
lean_dec(v_unused_2132_);
v___x_2126_ = v___x_2123_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_snd_2124_);
lean_dec(v___x_2123_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
lean_ctor_set(v___x_2126_, 0, v___x_2122_);
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2122_);
lean_ctor_set(v_reuseFailAlloc_2130_, 1, v_snd_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_del_object(v___x_2110_);
lean_dec(v_head_2108_);
lean_dec(v_p_2098_);
v___y_2103_ = v_a_2100_;
goto v___jp_2102_;
}
}
}
else
{
lean_dec_ref(v_path_2106_);
lean_dec(v_p_2098_);
v___y_2103_ = v_a_2100_;
goto v___jp_2102_;
}
}
else
{
lean_dec(v_path_2106_);
lean_dec(v_p_2098_);
v___y_2103_ = v_a_2100_;
goto v___jp_2102_;
}
v___jp_2102_:
{
lean_object* v_path_2104_; lean_object* v___x_2105_; 
v_path_2104_ = lean_ctor_get(v___x_2101_, 0);
lean_inc(v_path_2104_);
lean_dec_ref(v___x_2101_);
v___x_2105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2105_, 0, v_path_2104_);
lean_ctor_set(v___x_2105_, 1, v___y_2103_);
return v___x_2105_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths_getPath___boxed(lean_object* v_p_2136_, lean_object* v_depth_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lean_Level_Normalize_NormLevel_buildPaths_getPath(v_p_2136_, v_depth_2137_, v_a_2138_);
lean_dec(v_depth_2137_);
return v_res_2139_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Level_Normalize_NormLevel_buildPaths_spec__0(lean_object* v_init_2140_, lean_object* v_x_2141_, lean_object* v___y_2142_){
_start:
{
if (lean_obj_tag(v_x_2141_) == 0)
{
lean_object* v_k_2143_; lean_object* v_l_2144_; lean_object* v_r_2145_; lean_object* v___y_2147_; lean_object* v___x_2150_; lean_object* v_snd_2151_; lean_object* v___x_2152_; lean_object* v_path_2153_; 
v_k_2143_ = lean_ctor_get(v_x_2141_, 1);
lean_inc(v_k_2143_);
v_l_2144_ = lean_ctor_get(v_x_2141_, 3);
lean_inc(v_l_2144_);
v_r_2145_ = lean_ctor_get(v_x_2141_, 4);
lean_inc(v_r_2145_);
lean_dec_ref(v_x_2141_);
v___x_2150_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Level_Normalize_NormLevel_buildPaths_spec__0(v_init_2140_, v_l_2144_, v___y_2142_);
v_snd_2151_ = lean_ctor_get(v___x_2150_, 1);
lean_inc(v_snd_2151_);
lean_dec_ref(v___x_2150_);
v___x_2152_ = l_Std_DTreeMap_Internal_Impl_Const_get_x21___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__0(v_snd_2151_, v_k_2143_);
v_path_2153_ = lean_ctor_get(v___x_2152_, 0);
lean_inc(v_path_2153_);
lean_dec_ref(v___x_2152_);
if (lean_obj_tag(v_path_2153_) == 1)
{
lean_object* v_tail_2154_; 
v_tail_2154_ = lean_ctor_get(v_path_2153_, 1);
if (lean_obj_tag(v_tail_2154_) == 0)
{
lean_object* v_head_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2172_; 
v_head_2155_ = lean_ctor_get(v_path_2153_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v_path_2153_);
if (v_isSharedCheck_2172_ == 0)
{
lean_object* v_unused_2173_; 
v_unused_2173_ = lean_ctor_get(v_path_2153_, 1);
lean_dec(v_unused_2173_);
v___x_2157_ = v_path_2153_;
v_isShared_2158_ = v_isSharedCheck_2172_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_head_2155_);
lean_dec(v_path_2153_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2172_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v_fst_2163_; lean_object* v_snd_2164_; lean_object* v___x_2166_; 
v___x_2159_ = ((lean_object*)(l_Lean_Level_Normalize_NormLevel_buildPaths_getPath___closed__0));
lean_inc(v_k_2143_);
v___x_2160_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Lean_Level_Normalize_NormLevel_buildPaths_getPath_spec__1(v_k_2143_, v_head_2155_, v_k_2143_, v___x_2159_);
v___x_2161_ = l_List_lengthTR___redArg(v_k_2143_);
v___x_2162_ = l_Lean_Level_Normalize_NormLevel_buildPaths_getPath(v___x_2160_, v___x_2161_, v_snd_2151_);
lean_dec(v___x_2161_);
v_fst_2163_ = lean_ctor_get(v___x_2162_, 0);
lean_inc(v_fst_2163_);
v_snd_2164_ = lean_ctor_get(v___x_2162_, 1);
lean_inc(v_snd_2164_);
lean_dec_ref(v___x_2162_);
if (v_isShared_2158_ == 0)
{
lean_ctor_set(v___x_2157_, 1, v_fst_2163_);
v___x_2166_ = v___x_2157_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_head_2155_);
lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_fst_2163_);
v___x_2166_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
lean_object* v___x_2167_; lean_object* v_fst_2168_; lean_object* v_snd_2169_; 
v___x_2167_ = l_Lean_Level_Normalize_NormLevel_buildPaths_setPath(v_k_2143_, v___x_2166_, v_snd_2164_);
v_fst_2168_ = lean_ctor_get(v___x_2167_, 0);
lean_inc(v_fst_2168_);
v_snd_2169_ = lean_ctor_get(v___x_2167_, 1);
lean_inc(v_snd_2169_);
lean_dec_ref(v___x_2167_);
v_init_2140_ = v_fst_2168_;
v_x_2141_ = v_r_2145_;
v___y_2142_ = v_snd_2169_;
goto _start;
}
}
}
else
{
lean_dec_ref(v_path_2153_);
lean_dec(v_k_2143_);
v___y_2147_ = v_snd_2151_;
goto v___jp_2146_;
}
}
else
{
lean_dec(v_path_2153_);
lean_dec(v_k_2143_);
v___y_2147_ = v_snd_2151_;
goto v___jp_2146_;
}
v___jp_2146_:
{
lean_object* v___x_2148_; 
v___x_2148_ = lean_box(0);
v_init_2140_ = v___x_2148_;
v_x_2141_ = v_r_2145_;
v___y_2142_ = v___y_2147_;
goto _start;
}
}
else
{
lean_object* v___x_2174_; 
v___x_2174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2174_, 0, v_init_2140_);
lean_ctor_set(v___x_2174_, 1, v___y_2142_);
return v___x_2174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_buildPaths(lean_object* v_a_2175_){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_box(0);
lean_inc(v_a_2175_);
v___x_2177_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Lean_Level_Normalize_NormLevel_buildPaths_spec__0(v___x_2176_, v_a_2175_, v_a_2175_);
return v___x_2177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_modifyAt___redArg(lean_object* v_inst_2183_, lean_object* v_f_2184_, lean_object* v_n_2185_, lean_object* v_x_2186_){
_start:
{
if (lean_obj_tag(v_x_2186_) == 0)
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = lean_apply_1(v_f_2184_, v_inst_2183_);
v___x_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2188_, 0, v_n_2185_);
lean_ctor_set(v___x_2188_, 1, v___x_2187_);
v___x_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_x_2186_);
return v___x_2189_;
}
else
{
lean_object* v_head_2190_; lean_object* v_tail_2191_; lean_object* v_fst_2192_; lean_object* v_snd_2193_; uint8_t v___x_2194_; 
v_head_2190_ = lean_ctor_get(v_x_2186_, 0);
lean_inc(v_head_2190_);
v_tail_2191_ = lean_ctor_get(v_x_2186_, 1);
v_fst_2192_ = lean_ctor_get(v_head_2190_, 0);
v_snd_2193_ = lean_ctor_get(v_head_2190_, 1);
v___x_2194_ = l_Lean_Name_cmp(v_n_2185_, v_fst_2192_);
switch(v___x_2194_)
{
case 0:
{
lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2203_; 
v_isSharedCheck_2203_ = !lean_is_exclusive(v_head_2190_);
if (v_isSharedCheck_2203_ == 0)
{
lean_object* v_unused_2204_; lean_object* v_unused_2205_; 
v_unused_2204_ = lean_ctor_get(v_head_2190_, 1);
lean_dec(v_unused_2204_);
v_unused_2205_ = lean_ctor_get(v_head_2190_, 0);
lean_dec(v_unused_2205_);
v___x_2196_ = v_head_2190_;
v_isShared_2197_ = v_isSharedCheck_2203_;
goto v_resetjp_2195_;
}
else
{
lean_dec(v_head_2190_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2203_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2198_; lean_object* v___x_2200_; 
v___x_2198_ = lean_apply_1(v_f_2184_, v_inst_2183_);
if (v_isShared_2197_ == 0)
{
lean_ctor_set(v___x_2196_, 1, v___x_2198_);
lean_ctor_set(v___x_2196_, 0, v_n_2185_);
v___x_2200_ = v___x_2196_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v_n_2185_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v___x_2198_);
v___x_2200_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
lean_ctor_set(v___x_2201_, 1, v_x_2186_);
return v___x_2201_;
}
}
}
case 1:
{
lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2222_; 
lean_inc(v_snd_2193_);
lean_inc(v_fst_2192_);
lean_inc(v_tail_2191_);
lean_dec(v_n_2185_);
lean_dec(v_inst_2183_);
v_isSharedCheck_2222_ = !lean_is_exclusive(v_x_2186_);
if (v_isSharedCheck_2222_ == 0)
{
lean_object* v_unused_2223_; lean_object* v_unused_2224_; 
v_unused_2223_ = lean_ctor_get(v_x_2186_, 1);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_x_2186_, 0);
lean_dec(v_unused_2224_);
v___x_2207_ = v_x_2186_;
v_isShared_2208_ = v_isSharedCheck_2222_;
goto v_resetjp_2206_;
}
else
{
lean_dec(v_x_2186_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2222_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; uint8_t v_isShared_2211_; uint8_t v_isSharedCheck_2219_; 
v_isSharedCheck_2219_ = !lean_is_exclusive(v_head_2190_);
if (v_isSharedCheck_2219_ == 0)
{
lean_object* v_unused_2220_; lean_object* v_unused_2221_; 
v_unused_2220_ = lean_ctor_get(v_head_2190_, 1);
lean_dec(v_unused_2220_);
v_unused_2221_ = lean_ctor_get(v_head_2190_, 0);
lean_dec(v_unused_2221_);
v___x_2210_ = v_head_2190_;
v_isShared_2211_ = v_isSharedCheck_2219_;
goto v_resetjp_2209_;
}
else
{
lean_dec(v_head_2190_);
v___x_2210_ = lean_box(0);
v_isShared_2211_ = v_isSharedCheck_2219_;
goto v_resetjp_2209_;
}
v_resetjp_2209_:
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
v___x_2212_ = lean_apply_1(v_f_2184_, v_snd_2193_);
if (v_isShared_2211_ == 0)
{
lean_ctor_set(v___x_2210_, 1, v___x_2212_);
v___x_2214_ = v___x_2210_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_fst_2192_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v___x_2212_);
v___x_2214_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2216_; 
if (v_isShared_2208_ == 0)
{
lean_ctor_set(v___x_2207_, 0, v___x_2214_);
v___x_2216_ = v___x_2207_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2217_, 1, v_tail_2191_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
default: 
{
lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2232_; 
lean_inc(v_tail_2191_);
v_isSharedCheck_2232_ = !lean_is_exclusive(v_x_2186_);
if (v_isSharedCheck_2232_ == 0)
{
lean_object* v_unused_2233_; lean_object* v_unused_2234_; 
v_unused_2233_ = lean_ctor_get(v_x_2186_, 1);
lean_dec(v_unused_2233_);
v_unused_2234_ = lean_ctor_get(v_x_2186_, 0);
lean_dec(v_unused_2234_);
v___x_2226_ = v_x_2186_;
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
else
{
lean_dec(v_x_2186_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2232_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2228_; lean_object* v___x_2230_; 
v___x_2228_ = l_Lean_Level_Normalize_modifyAt___redArg(v_inst_2183_, v_f_2184_, v_n_2185_, v_tail_2191_);
if (v_isShared_2227_ == 0)
{
lean_ctor_set(v___x_2226_, 1, v___x_2228_);
v___x_2230_ = v___x_2226_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_head_2190_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v___x_2228_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_modifyAt(lean_object* v_00_u03b1_2235_, lean_object* v_inst_2236_, lean_object* v_f_2237_, lean_object* v_n_2238_, lean_object* v_x_2239_){
_start:
{
lean_object* v___x_2240_; 
v___x_2240_ = l_Lean_Level_Normalize_modifyAt___redArg(v_inst_2236_, v_f_2237_, v_n_2238_, v_x_2239_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_modify___lam__0(lean_object* v___x_2241_, lean_object* v_f_2242_, lean_object* v_head_2243_, lean_object* v_t_2244_){
_start:
{
lean_object* v_const_2245_; lean_object* v_var_2246_; lean_object* v_child_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2255_; 
v_const_2245_ = lean_ctor_get(v_t_2244_, 0);
v_var_2246_ = lean_ctor_get(v_t_2244_, 1);
v_child_2247_ = lean_ctor_get(v_t_2244_, 2);
v_isSharedCheck_2255_ = !lean_is_exclusive(v_t_2244_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2249_ = v_t_2244_;
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_child_2247_);
lean_inc(v_var_2246_);
lean_inc(v_const_2245_);
lean_dec(v_t_2244_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2255_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = l_Lean_Level_Normalize_modifyAt___redArg(v___x_2241_, v_f_2242_, v_head_2243_, v_child_2247_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 2, v___x_2251_);
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_const_2245_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_var_2246_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v___x_2251_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_modify(lean_object* v_path_2256_, lean_object* v_f_2257_, lean_object* v_t_2258_){
_start:
{
if (lean_obj_tag(v_path_2256_) == 0)
{
lean_object* v___x_2259_; 
v___x_2259_ = lean_apply_1(v_f_2257_, v_t_2258_);
return v___x_2259_;
}
else
{
lean_object* v_head_2260_; lean_object* v_tail_2261_; lean_object* v___x_2262_; lean_object* v___f_2263_; 
v_head_2260_ = lean_ctor_get(v_path_2256_, 0);
lean_inc(v_head_2260_);
v_tail_2261_ = lean_ctor_get(v_path_2256_, 1);
lean_inc(v_tail_2261_);
lean_dec_ref(v_path_2256_);
v___x_2262_ = ((lean_object*)(l_Lean_Level_Normalize_instInhabitedTree_default));
v___f_2263_ = lean_alloc_closure((void*)(l_Lean_Level_Normalize_Tree_modify___lam__0), 4, 3);
lean_closure_set(v___f_2263_, 0, v___x_2262_);
lean_closure_set(v___f_2263_, 1, v_f_2257_);
lean_closure_set(v___f_2263_, 2, v_head_2260_);
v_path_2256_ = v_tail_2261_;
v_f_2257_ = v___f_2263_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0___lam__0(lean_object* v_const_2265_, lean_object* v_var_2266_, lean_object* v_t_2267_){
_start:
{
lean_object* v_child_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_child_2268_ = lean_ctor_get(v_t_2267_, 2);
v_isSharedCheck_2275_ = !lean_is_exclusive(v_t_2267_);
if (v_isSharedCheck_2275_ == 0)
{
lean_object* v_unused_2276_; lean_object* v_unused_2277_; 
v_unused_2276_ = lean_ctor_get(v_t_2267_, 1);
lean_dec(v_unused_2276_);
v_unused_2277_ = lean_ctor_get(v_t_2267_, 0);
lean_dec(v_unused_2277_);
v___x_2270_ = v_t_2267_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_child_2268_);
lean_dec(v_t_2267_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
lean_ctor_set(v___x_2270_, 1, v_var_2266_);
lean_ctor_set(v___x_2270_, 0, v_const_2265_);
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_const_2265_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_var_2266_);
lean_ctor_set(v_reuseFailAlloc_2274_, 2, v_child_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0(lean_object* v_init_2278_, lean_object* v_x_2279_){
_start:
{
if (lean_obj_tag(v_x_2279_) == 0)
{
lean_object* v_v_2280_; lean_object* v_l_2281_; lean_object* v_r_2282_; lean_object* v_path_2283_; lean_object* v_const_2284_; lean_object* v_var_2285_; lean_object* v___f_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; 
v_v_2280_ = lean_ctor_get(v_x_2279_, 2);
lean_inc(v_v_2280_);
v_l_2281_ = lean_ctor_get(v_x_2279_, 3);
lean_inc(v_l_2281_);
v_r_2282_ = lean_ctor_get(v_x_2279_, 4);
lean_inc(v_r_2282_);
lean_dec_ref(v_x_2279_);
v_path_2283_ = lean_ctor_get(v_v_2280_, 0);
lean_inc(v_path_2283_);
v_const_2284_ = lean_ctor_get(v_v_2280_, 1);
lean_inc(v_const_2284_);
v_var_2285_ = lean_ctor_get(v_v_2280_, 2);
lean_inc(v_var_2285_);
lean_dec(v_v_2280_);
v___f_2286_ = lean_alloc_closure((void*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0___lam__0), 3, 2);
lean_closure_set(v___f_2286_, 0, v_const_2284_);
lean_closure_set(v___f_2286_, 1, v_var_2285_);
v___x_2287_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0(v_init_2278_, v_l_2281_);
v___x_2288_ = l_Lean_Level_Normalize_Tree_modify(v_path_2283_, v___f_2286_, v___x_2287_);
v_init_2278_ = v___x_2288_;
v_x_2279_ = v_r_2282_;
goto _start;
}
else
{
return v_init_2278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_NormLevel_toTree(lean_object* v_acc_2290_){
_start:
{
lean_object* v___x_2291_; lean_object* v_snd_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; 
v___x_2291_ = l_Lean_Level_Normalize_NormLevel_buildPaths(v_acc_2290_);
v_snd_2292_ = lean_ctor_get(v___x_2291_, 1);
lean_inc(v_snd_2292_);
lean_dec_ref(v___x_2291_);
v___x_2293_ = ((lean_object*)(l_Lean_Level_Normalize_instInhabitedTree_default___closed__0));
v___x_2294_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0(v___x_2293_, v_snd_2292_);
return v___x_2294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0(lean_object* v_init_2295_, lean_object* v_t_2296_){
_start:
{
lean_object* v___x_2297_; 
v___x_2297_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Level_Normalize_NormLevel_toTree_spec__0_spec__0(v_init_2295_, v_t_2296_);
return v___x_2297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_treeVarDedup(lean_object* v_x_2298_, lean_object* v_x_2299_){
_start:
{
if (lean_obj_tag(v_x_2298_) == 0)
{
lean_dec(v_x_2299_);
return v_x_2298_;
}
else
{
if (lean_obj_tag(v_x_2299_) == 0)
{
return v_x_2298_;
}
else
{
lean_object* v_head_2300_; lean_object* v_head_2301_; lean_object* v_tail_2302_; lean_object* v_tail_2303_; lean_object* v_var_2304_; lean_object* v_offset_2305_; lean_object* v_fst_2306_; uint8_t v___x_2307_; 
v_head_2300_ = lean_ctor_get(v_x_2298_, 0);
v_head_2301_ = lean_ctor_get(v_x_2299_, 0);
v_tail_2302_ = lean_ctor_get(v_x_2298_, 1);
v_tail_2303_ = lean_ctor_get(v_x_2299_, 1);
v_var_2304_ = lean_ctor_get(v_head_2300_, 0);
v_offset_2305_ = lean_ctor_get(v_head_2300_, 1);
v_fst_2306_ = lean_ctor_get(v_head_2301_, 0);
v___x_2307_ = l_Lean_Name_cmp(v_var_2304_, v_fst_2306_);
switch(v___x_2307_)
{
case 0:
{
lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
lean_inc(v_tail_2302_);
lean_inc(v_head_2300_);
v_isSharedCheck_2315_ = !lean_is_exclusive(v_x_2298_);
if (v_isSharedCheck_2315_ == 0)
{
lean_object* v_unused_2316_; lean_object* v_unused_2317_; 
v_unused_2316_ = lean_ctor_get(v_x_2298_, 1);
lean_dec(v_unused_2316_);
v_unused_2317_ = lean_ctor_get(v_x_2298_, 0);
lean_dec(v_unused_2317_);
v___x_2309_ = v_x_2298_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_dec(v_x_2298_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v___x_2311_; lean_object* v___x_2313_; 
v___x_2311_ = l_Lean_Level_Normalize_treeVarDedup(v_tail_2302_, v_x_2299_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 1, v___x_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_head_2300_);
lean_ctor_set(v_reuseFailAlloc_2314_, 1, v___x_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
case 1:
{
lean_object* v___x_2319_; uint8_t v_isShared_2320_; uint8_t v_isSharedCheck_2328_; 
lean_inc(v_tail_2303_);
lean_inc(v_tail_2302_);
lean_inc(v_head_2300_);
lean_dec_ref(v_x_2298_);
v_isSharedCheck_2328_ = !lean_is_exclusive(v_x_2299_);
if (v_isSharedCheck_2328_ == 0)
{
lean_object* v_unused_2329_; lean_object* v_unused_2330_; 
v_unused_2329_ = lean_ctor_get(v_x_2299_, 1);
lean_dec(v_unused_2329_);
v_unused_2330_ = lean_ctor_get(v_x_2299_, 0);
lean_dec(v_unused_2330_);
v___x_2319_ = v_x_2299_;
v_isShared_2320_ = v_isSharedCheck_2328_;
goto v_resetjp_2318_;
}
else
{
lean_dec(v_x_2299_);
v___x_2319_ = lean_box(0);
v_isShared_2320_ = v_isSharedCheck_2328_;
goto v_resetjp_2318_;
}
v_resetjp_2318_:
{
lean_object* v___x_2321_; uint8_t v___x_2322_; 
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = lean_nat_dec_eq(v_offset_2305_, v___x_2321_);
if (v___x_2322_ == 0)
{
lean_object* v___x_2323_; lean_object* v___x_2325_; 
v___x_2323_ = l_Lean_Level_Normalize_treeVarDedup(v_tail_2302_, v_tail_2303_);
if (v_isShared_2320_ == 0)
{
lean_ctor_set(v___x_2319_, 1, v___x_2323_);
lean_ctor_set(v___x_2319_, 0, v_head_2300_);
v___x_2325_ = v___x_2319_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_head_2300_);
lean_ctor_set(v_reuseFailAlloc_2326_, 1, v___x_2323_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
else
{
lean_del_object(v___x_2319_);
lean_dec(v_head_2300_);
v_x_2298_ = v_tail_2302_;
v_x_2299_ = v_tail_2303_;
goto _start;
}
}
}
default: 
{
lean_inc(v_tail_2303_);
lean_dec_ref(v_x_2299_);
v_x_2299_ = v_tail_2303_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_treeVarDedup_match__1_splitter___redArg(lean_object* v_x_2332_, lean_object* v_x_2333_, lean_object* v_h__1_2334_, lean_object* v_h__2_2335_, lean_object* v_h__3_2336_){
_start:
{
if (lean_obj_tag(v_x_2332_) == 0)
{
lean_object* v___x_2337_; 
lean_dec(v_h__3_2336_);
lean_dec(v_h__2_2335_);
v___x_2337_ = lean_apply_1(v_h__1_2334_, v_x_2333_);
return v___x_2337_;
}
else
{
lean_dec(v_h__1_2334_);
if (lean_obj_tag(v_x_2333_) == 0)
{
lean_object* v___x_2338_; 
lean_dec(v_h__3_2336_);
v___x_2338_ = lean_apply_2(v_h__2_2335_, v_x_2332_, lean_box(0));
return v___x_2338_;
}
else
{
lean_object* v_head_2339_; lean_object* v_tail_2340_; lean_object* v_head_2341_; lean_object* v_tail_2342_; lean_object* v___x_2343_; 
lean_dec(v_h__2_2335_);
v_head_2339_ = lean_ctor_get(v_x_2332_, 0);
lean_inc(v_head_2339_);
v_tail_2340_ = lean_ctor_get(v_x_2332_, 1);
lean_inc(v_tail_2340_);
lean_dec_ref(v_x_2332_);
v_head_2341_ = lean_ctor_get(v_x_2333_, 0);
lean_inc(v_head_2341_);
v_tail_2342_ = lean_ctor_get(v_x_2333_, 1);
lean_inc(v_tail_2342_);
lean_dec_ref(v_x_2333_);
v___x_2343_ = lean_apply_4(v_h__3_2336_, v_head_2339_, v_tail_2340_, v_head_2341_, v_tail_2342_);
return v___x_2343_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_treeVarDedup_match__1_splitter(lean_object* v_motive_2344_, lean_object* v_x_2345_, lean_object* v_x_2346_, lean_object* v_h__1_2347_, lean_object* v_h__2_2348_, lean_object* v_h__3_2349_){
_start:
{
if (lean_obj_tag(v_x_2345_) == 0)
{
lean_object* v___x_2350_; 
lean_dec(v_h__3_2349_);
lean_dec(v_h__2_2348_);
v___x_2350_ = lean_apply_1(v_h__1_2347_, v_x_2346_);
return v___x_2350_;
}
else
{
lean_dec(v_h__1_2347_);
if (lean_obj_tag(v_x_2346_) == 0)
{
lean_object* v___x_2351_; 
lean_dec(v_h__3_2349_);
v___x_2351_ = lean_apply_2(v_h__2_2348_, v_x_2345_, lean_box(0));
return v___x_2351_;
}
else
{
lean_object* v_head_2352_; lean_object* v_tail_2353_; lean_object* v_head_2354_; lean_object* v_tail_2355_; lean_object* v___x_2356_; 
lean_dec(v_h__2_2348_);
v_head_2352_ = lean_ctor_get(v_x_2345_, 0);
lean_inc(v_head_2352_);
v_tail_2353_ = lean_ctor_get(v_x_2345_, 1);
lean_inc(v_tail_2353_);
lean_dec_ref(v_x_2345_);
v_head_2354_ = lean_ctor_get(v_x_2346_, 0);
lean_inc(v_head_2354_);
v_tail_2355_ = lean_ctor_get(v_x_2346_, 1);
lean_inc(v_tail_2355_);
lean_dec_ref(v_x_2346_);
v___x_2356_ = lean_apply_4(v_h__3_2349_, v_head_2352_, v_tail_2353_, v_head_2354_, v_tail_2355_);
return v___x_2356_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_reify_mkMax(lean_object* v_l_2357_, lean_object* v_a_2358_){
_start:
{
if (lean_obj_tag(v_a_2358_) == 0)
{
return v_l_2357_;
}
else
{
lean_object* v_val_2359_; lean_object* v___x_2360_; 
v_val_2359_ = lean_ctor_get(v_a_2358_, 0);
lean_inc(v_val_2359_);
lean_dec_ref(v_a_2358_);
v___x_2360_ = l_Lean_Level_max___override(v_l_2357_, v_val_2359_);
return v___x_2360_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2_spec__3(lean_object* v_as_2361_, size_t v_i_2362_, size_t v_stop_2363_, lean_object* v_b_2364_){
_start:
{
uint8_t v___x_2365_; 
v___x_2365_ = lean_usize_dec_eq(v_i_2362_, v_stop_2363_);
if (v___x_2365_ == 0)
{
size_t v___x_2366_; size_t v___x_2367_; lean_object* v___x_2368_; lean_object* v_var_2369_; lean_object* v_offset_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2366_ = ((size_t)1ULL);
v___x_2367_ = lean_usize_sub(v_i_2362_, v___x_2366_);
v___x_2368_ = lean_array_uget_borrowed(v_as_2361_, v___x_2367_);
v_var_2369_ = lean_ctor_get(v___x_2368_, 0);
v_offset_2370_ = lean_ctor_get(v___x_2368_, 1);
lean_inc(v_var_2369_);
v___x_2371_ = l_Lean_Level_param___override(v_var_2369_);
lean_inc(v_offset_2370_);
v___x_2372_ = l_Lean_Level_addOffset(v___x_2371_, v_offset_2370_);
v___x_2373_ = l_Lean_Level_Normalize_Tree_reify_mkMax(v___x_2372_, v_b_2364_);
v___x_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
v_i_2362_ = v___x_2367_;
v_b_2364_ = v___x_2374_;
goto _start;
}
else
{
return v_b_2364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2_spec__3___boxed(lean_object* v_as_2376_, lean_object* v_i_2377_, lean_object* v_stop_2378_, lean_object* v_b_2379_){
_start:
{
size_t v_i_boxed_2380_; size_t v_stop_boxed_2381_; lean_object* v_res_2382_; 
v_i_boxed_2380_ = lean_unbox_usize(v_i_2377_);
lean_dec(v_i_2377_);
v_stop_boxed_2381_ = lean_unbox_usize(v_stop_2378_);
lean_dec(v_stop_2378_);
v_res_2382_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2_spec__3(v_as_2376_, v_i_boxed_2380_, v_stop_boxed_2381_, v_b_2379_);
lean_dec_ref(v_as_2376_);
return v_res_2382_;
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2(lean_object* v_init_2383_, lean_object* v_l_2384_){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; uint8_t v___x_2388_; 
v___x_2385_ = lean_array_mk(v_l_2384_);
v___x_2386_ = lean_array_get_size(v___x_2385_);
v___x_2387_ = lean_unsigned_to_nat(0u);
v___x_2388_ = lean_nat_dec_lt(v___x_2387_, v___x_2386_);
if (v___x_2388_ == 0)
{
lean_dec_ref(v___x_2385_);
return v_init_2383_;
}
else
{
size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = lean_usize_of_nat(v___x_2386_);
v___x_2390_ = ((size_t)0ULL);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2_spec__3(v___x_2385_, v___x_2389_, v___x_2390_, v_init_2383_);
lean_dec_ref(v___x_2385_);
return v___x_2391_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1(lean_object* v_init_2392_, lean_object* v_l_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; uint8_t v___x_2397_; 
v___x_2394_ = lean_array_mk(v_l_2393_);
v___x_2395_ = lean_array_get_size(v___x_2394_);
v___x_2396_ = lean_unsigned_to_nat(0u);
v___x_2397_ = lean_nat_dec_lt(v___x_2396_, v___x_2395_);
if (v___x_2397_ == 0)
{
lean_dec_ref(v___x_2394_);
return v_init_2392_;
}
else
{
size_t v___x_2398_; size_t v___x_2399_; lean_object* v___x_2400_; 
v___x_2398_ = lean_usize_of_nat(v___x_2395_);
v___x_2399_ = ((size_t)0ULL);
v___x_2400_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1_spec__1(v___x_2394_, v___x_2398_, v___x_2399_, v_init_2392_);
lean_dec_ref(v___x_2394_);
return v___x_2400_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_reify(lean_object* v_x_2401_){
_start:
{
lean_object* v_const_2402_; lean_object* v_var_2403_; lean_object* v_child_2404_; lean_object* v___x_2405_; lean_object* v_l_2406_; lean_object* v___x_2407_; lean_object* v_l_2408_; 
v_const_2402_ = lean_ctor_get(v_x_2401_, 0);
lean_inc(v_const_2402_);
v_var_2403_ = lean_ctor_get(v_x_2401_, 1);
lean_inc(v_var_2403_);
v_child_2404_ = lean_ctor_get(v_x_2401_, 2);
lean_inc_n(v_child_2404_, 2);
lean_dec_ref(v_x_2401_);
v___x_2405_ = lean_box(0);
v_l_2406_ = l_List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1(v___x_2405_, v_child_2404_);
v___x_2407_ = l_Lean_Level_Normalize_treeVarDedup(v_var_2403_, v_child_2404_);
v_l_2408_ = l_List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__2(v_l_2406_, v___x_2407_);
if (lean_obj_tag(v_l_2408_) == 0)
{
lean_object* v___x_2409_; 
v___x_2409_ = l_Lean_Level_ofNat(v_const_2402_);
lean_dec(v_const_2402_);
return v___x_2409_;
}
else
{
lean_object* v_val_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; 
v_val_2410_ = lean_ctor_get(v_l_2408_, 0);
lean_inc(v_val_2410_);
lean_dec_ref(v_l_2408_);
v___x_2411_ = lean_unsigned_to_nat(0u);
v___x_2412_ = lean_nat_dec_eq(v_const_2402_, v___x_2411_);
if (v___x_2412_ == 0)
{
lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2413_ = l_Lean_Level_ofNat(v_const_2402_);
lean_dec(v_const_2402_);
v___x_2414_ = l_Lean_Level_max___override(v___x_2413_, v_val_2410_);
return v___x_2414_;
}
else
{
lean_dec(v_const_2402_);
return v_val_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_Normalize_Tree_reify_mkChild(lean_object* v_x_2415_, lean_object* v_x_2416_){
_start:
{
lean_object* v_fst_2417_; lean_object* v_snd_2418_; lean_object* v___x_2419_; 
v_fst_2417_ = lean_ctor_get(v_x_2415_, 0);
lean_inc(v_fst_2417_);
v_snd_2418_ = lean_ctor_get(v_x_2415_, 1);
lean_inc(v_snd_2418_);
lean_dec_ref(v_x_2415_);
v___x_2419_ = l_Lean_Level_Normalize_Tree_reify(v_snd_2418_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2420_ = l_Lean_Level_param___override(v_fst_2417_);
v___x_2421_ = l_Lean_Level_Normalize_Tree_reify_mkMax(v___x_2420_, v_x_2416_);
v___x_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2422_, 0, v___x_2421_);
return v___x_2422_;
}
else
{
lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; 
v___x_2423_ = l_Lean_Level_param___override(v_fst_2417_);
v___x_2424_ = l_Lean_Level_imax___override(v___x_2419_, v___x_2423_);
v___x_2425_ = l_Lean_Level_Normalize_Tree_reify_mkMax(v___x_2424_, v_x_2416_);
v___x_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2426_, 0, v___x_2425_);
return v___x_2426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1_spec__1(lean_object* v_as_2427_, size_t v_i_2428_, size_t v_stop_2429_, lean_object* v_b_2430_){
_start:
{
uint8_t v___x_2431_; 
v___x_2431_ = lean_usize_dec_eq(v_i_2428_, v_stop_2429_);
if (v___x_2431_ == 0)
{
size_t v___x_2432_; size_t v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; 
v___x_2432_ = ((size_t)1ULL);
v___x_2433_ = lean_usize_sub(v_i_2428_, v___x_2432_);
v___x_2434_ = lean_array_uget_borrowed(v_as_2427_, v___x_2433_);
lean_inc(v___x_2434_);
v___x_2435_ = l_Lean_Level_Normalize_Tree_reify_mkChild(v___x_2434_, v_b_2430_);
v_i_2428_ = v___x_2433_;
v_b_2430_ = v___x_2435_;
goto _start;
}
else
{
return v_b_2430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1_spec__1___boxed(lean_object* v_as_2437_, lean_object* v_i_2438_, lean_object* v_stop_2439_, lean_object* v_b_2440_){
_start:
{
size_t v_i_boxed_2441_; size_t v_stop_boxed_2442_; lean_object* v_res_2443_; 
v_i_boxed_2441_ = lean_unbox_usize(v_i_2438_);
lean_dec(v_i_2438_);
v_stop_boxed_2442_ = lean_unbox_usize(v_stop_2439_);
lean_dec(v_stop_2439_);
v_res_2443_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00List_foldrTR___at___00Lean_Level_Normalize_Tree_reify_spec__1_spec__1(v_as_2437_, v_i_boxed_2441_, v_stop_boxed_2442_, v_b_2440_);
lean_dec_ref(v_as_2437_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__4_splitter___redArg(lean_object* v_x_2444_, lean_object* v_x_2445_, lean_object* v_h__1_2446_){
_start:
{
lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v___x_2449_; 
v_fst_2447_ = lean_ctor_get(v_x_2444_, 0);
lean_inc(v_fst_2447_);
v_snd_2448_ = lean_ctor_get(v_x_2444_, 1);
lean_inc(v_snd_2448_);
lean_dec_ref(v_x_2444_);
v___x_2449_ = lean_apply_3(v_h__1_2446_, v_fst_2447_, v_snd_2448_, v_x_2445_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__4_splitter(lean_object* v_motive_2450_, lean_object* v_x_2451_, lean_object* v_x_2452_, lean_object* v_h__1_2453_){
_start:
{
lean_object* v_fst_2454_; lean_object* v_snd_2455_; lean_object* v___x_2456_; 
v_fst_2454_ = lean_ctor_get(v_x_2451_, 0);
lean_inc(v_fst_2454_);
v_snd_2455_ = lean_ctor_get(v_x_2451_, 1);
lean_inc(v_snd_2455_);
lean_dec_ref(v_x_2451_);
v___x_2456_ = lean_apply_3(v_h__1_2453_, v_fst_2454_, v_snd_2455_, v_x_2452_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__1_splitter___redArg(lean_object* v_x_2457_, lean_object* v_h__1_2458_, lean_object* v_h__2_2459_){
_start:
{
if (lean_obj_tag(v_x_2457_) == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
lean_dec(v_h__2_2459_);
v___x_2460_ = lean_box(0);
v___x_2461_ = lean_apply_1(v_h__1_2458_, v___x_2460_);
return v___x_2461_;
}
else
{
lean_object* v___x_2462_; 
lean_dec(v_h__1_2458_);
v___x_2462_ = lean_apply_2(v_h__2_2459_, v_x_2457_, lean_box(0));
return v___x_2462_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__1_splitter(lean_object* v_motive_2463_, lean_object* v_x_2464_, lean_object* v_h__1_2465_, lean_object* v_h__2_2466_){
_start:
{
if (lean_obj_tag(v_x_2464_) == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; 
lean_dec(v_h__2_2466_);
v___x_2467_ = lean_box(0);
v___x_2468_ = lean_apply_1(v_h__1_2465_, v___x_2467_);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; 
lean_dec(v_h__1_2465_);
v___x_2469_ = lean_apply_2(v_h__2_2466_, v_x_2464_, lean_box(0));
return v___x_2469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__6_splitter___redArg(lean_object* v_x_2470_, lean_object* v_h__1_2471_){
_start:
{
lean_object* v_const_2472_; lean_object* v_var_2473_; lean_object* v_child_2474_; lean_object* v___x_2475_; 
v_const_2472_ = lean_ctor_get(v_x_2470_, 0);
lean_inc(v_const_2472_);
v_var_2473_ = lean_ctor_get(v_x_2470_, 1);
lean_inc(v_var_2473_);
v_child_2474_ = lean_ctor_get(v_x_2470_, 2);
lean_inc(v_child_2474_);
lean_dec_ref(v_x_2470_);
v___x_2475_ = lean_apply_3(v_h__1_2471_, v_const_2472_, v_var_2473_, v_child_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_match__6_splitter(lean_object* v_motive_2476_, lean_object* v_x_2477_, lean_object* v_h__1_2478_){
_start:
{
lean_object* v_const_2479_; lean_object* v_var_2480_; lean_object* v_child_2481_; lean_object* v___x_2482_; 
v_const_2479_ = lean_ctor_get(v_x_2477_, 0);
lean_inc(v_const_2479_);
v_var_2480_ = lean_ctor_get(v_x_2477_, 1);
lean_inc(v_var_2480_);
v_child_2481_ = lean_ctor_get(v_x_2477_, 2);
lean_inc(v_child_2481_);
lean_dec_ref(v_x_2477_);
v___x_2482_ = lean_apply_3(v_h__1_2478_, v_const_2479_, v_var_2480_, v_child_2481_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__List_map__unattach_match__1_splitter___redArg(lean_object* v_x_2483_, lean_object* v_h__1_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = lean_apply_2(v_h__1_2484_, v_x_2483_, lean_box(0));
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__List_map__unattach_match__1_splitter(lean_object* v_00_u03b1_2486_, lean_object* v_P_2487_, lean_object* v_motive_2488_, lean_object* v_x_2489_, lean_object* v_h__1_2490_){
_start:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_apply_2(v_h__1_2490_, v_x_2489_, lean_box(0));
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_mkMax_match__1_splitter___redArg(lean_object* v_x_2492_, lean_object* v_h__1_2493_, lean_object* v_h__2_2494_){
_start:
{
if (lean_obj_tag(v_x_2492_) == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec(v_h__2_2494_);
v___x_2495_ = lean_box(0);
v___x_2496_ = lean_apply_1(v_h__1_2493_, v___x_2495_);
return v___x_2496_;
}
else
{
lean_object* v_val_2497_; lean_object* v___x_2498_; 
lean_dec(v_h__1_2493_);
v_val_2497_ = lean_ctor_get(v_x_2492_, 0);
lean_inc(v_val_2497_);
lean_dec_ref(v_x_2492_);
v___x_2498_ = lean_apply_1(v_h__2_2494_, v_val_2497_);
return v___x_2498_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Level_0__Lean_Level_Normalize_Tree_reify_mkMax_match__1_splitter(lean_object* v_motive_2499_, lean_object* v_x_2500_, lean_object* v_h__1_2501_, lean_object* v_h__2_2502_){
_start:
{
if (lean_obj_tag(v_x_2500_) == 0)
{
lean_object* v___x_2503_; lean_object* v___x_2504_; 
lean_dec(v_h__2_2502_);
v___x_2503_ = lean_box(0);
v___x_2504_ = lean_apply_1(v_h__1_2501_, v___x_2503_);
return v___x_2504_;
}
else
{
lean_object* v_val_2505_; lean_object* v___x_2506_; 
lean_dec(v_h__1_2501_);
v_val_2505_ = lean_ctor_get(v_x_2500_, 0);
lean_inc(v_val_2505_);
lean_dec_ref(v_x_2500_);
v___x_2506_ = lean_apply_1(v_h__2_2502_, v_val_2505_);
return v___x_2506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_normalize_x27(lean_object* v_l_2507_){
_start:
{
uint8_t v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2508_ = 1;
v___x_2509_ = l_Lean_Level_Normalize_normalize(v_l_2507_, v___x_2508_);
v___x_2510_ = l_Lean_Level_Normalize_NormLevel_toTree(v___x_2509_);
v___x_2511_ = l_Lean_Level_Normalize_Tree_reify(v___x_2510_);
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___redArg(lean_object* v_t_2512_, lean_object* v_k_2513_){
_start:
{
if (lean_obj_tag(v_t_2512_) == 0)
{
lean_object* v_k_2514_; lean_object* v_v_2515_; lean_object* v_l_2516_; lean_object* v_r_2517_; uint8_t v___x_2518_; 
v_k_2514_ = lean_ctor_get(v_t_2512_, 1);
v_v_2515_ = lean_ctor_get(v_t_2512_, 2);
v_l_2516_ = lean_ctor_get(v_t_2512_, 3);
v_r_2517_ = lean_ctor_get(v_t_2512_, 4);
v___x_2518_ = l_List_compareLex___at___00Lean_Level_Normalize_NormLevel_addVar_spec__0(v_k_2513_, v_k_2514_);
switch(v___x_2518_)
{
case 0:
{
v_t_2512_ = v_l_2516_;
goto _start;
}
case 1:
{
lean_object* v___x_2520_; 
lean_inc(v_v_2515_);
v___x_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2520_, 0, v_v_2515_);
return v___x_2520_;
}
default: 
{
v_t_2512_ = v_r_2517_;
goto _start;
}
}
}
else
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_box(0);
return v___x_2522_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___redArg___boxed(lean_object* v_t_2523_, lean_object* v_k_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___redArg(v_t_2523_, v_k_2524_);
lean_dec(v_k_2524_);
lean_dec(v_t_2523_);
return v_res_2525_;
}
}
LEAN_EXPORT uint8_t l_List_beq___at___00Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1_spec__1(lean_object* v_x_2526_, lean_object* v_x_2527_){
_start:
{
if (lean_obj_tag(v_x_2526_) == 0)
{
if (lean_obj_tag(v_x_2527_) == 0)
{
uint8_t v___x_2528_; 
v___x_2528_ = 1;
return v___x_2528_;
}
else
{
uint8_t v___x_2529_; 
v___x_2529_ = 0;
return v___x_2529_;
}
}
else
{
if (lean_obj_tag(v_x_2527_) == 0)
{
uint8_t v___x_2530_; 
v___x_2530_ = 0;
return v___x_2530_;
}
else
{
lean_object* v_head_2531_; lean_object* v_tail_2532_; lean_object* v_head_2533_; lean_object* v_tail_2534_; uint8_t v___x_2535_; 
v_head_2531_ = lean_ctor_get(v_x_2526_, 0);
v_tail_2532_ = lean_ctor_get(v_x_2526_, 1);
v_head_2533_ = lean_ctor_get(v_x_2527_, 0);
v_tail_2534_ = lean_ctor_get(v_x_2527_, 1);
v___x_2535_ = l_Lean_Level_Normalize_instBEqVarNode_beq(v_head_2531_, v_head_2533_);
if (v___x_2535_ == 0)
{
return v___x_2535_;
}
else
{
v_x_2526_ = v_tail_2532_;
v_x_2527_ = v_tail_2534_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_beq___at___00Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1_spec__1___boxed(lean_object* v_x_2537_, lean_object* v_x_2538_){
_start:
{
uint8_t v_res_2539_; lean_object* v_r_2540_; 
v_res_2539_ = l_List_beq___at___00Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1_spec__1(v_x_2537_, v_x_2538_);
lean_dec(v_x_2538_);
lean_dec(v_x_2537_);
v_r_2540_ = lean_box(v_res_2539_);
return v_r_2540_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1(lean_object* v_x_2541_, lean_object* v_x_2542_){
_start:
{
if (lean_obj_tag(v_x_2541_) == 0)
{
if (lean_obj_tag(v_x_2542_) == 0)
{
uint8_t v___x_2543_; 
v___x_2543_ = 1;
return v___x_2543_;
}
else
{
uint8_t v___x_2544_; 
v___x_2544_ = 0;
return v___x_2544_;
}
}
else
{
if (lean_obj_tag(v_x_2542_) == 0)
{
uint8_t v___x_2545_; 
v___x_2545_ = 0;
return v___x_2545_;
}
else
{
lean_object* v_val_2546_; lean_object* v_val_2547_; lean_object* v_const_2548_; lean_object* v_var_2549_; lean_object* v_const_2550_; lean_object* v_var_2551_; uint8_t v___x_2552_; 
v_val_2546_ = lean_ctor_get(v_x_2541_, 0);
v_val_2547_ = lean_ctor_get(v_x_2542_, 0);
v_const_2548_ = lean_ctor_get(v_val_2546_, 1);
v_var_2549_ = lean_ctor_get(v_val_2546_, 2);
v_const_2550_ = lean_ctor_get(v_val_2547_, 1);
v_var_2551_ = lean_ctor_get(v_val_2547_, 2);
v___x_2552_ = lean_nat_dec_eq(v_const_2548_, v_const_2550_);
if (v___x_2552_ == 0)
{
return v___x_2552_;
}
else
{
uint8_t v___x_2553_; 
v___x_2553_ = l_List_beq___at___00Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1_spec__1(v_var_2549_, v_var_2551_);
return v___x_2553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1___boxed(lean_object* v_x_2554_, lean_object* v_x_2555_){
_start:
{
uint8_t v_res_2556_; lean_object* v_r_2557_; 
v_res_2556_ = l_Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1(v_x_2554_, v_x_2555_);
lean_dec(v_x_2555_);
lean_dec(v_x_2554_);
v_r_2557_ = lean_box(v_res_2556_);
return v_r_2557_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2(lean_object* v___x_2558_, lean_object* v_init_2559_, lean_object* v_x_2560_){
_start:
{
if (lean_obj_tag(v_x_2560_) == 0)
{
lean_object* v_k_2561_; lean_object* v_v_2562_; lean_object* v_l_2563_; lean_object* v_r_2564_; lean_object* v___x_2565_; 
v_k_2561_ = lean_ctor_get(v_x_2560_, 1);
v_v_2562_ = lean_ctor_get(v_x_2560_, 2);
v_l_2563_ = lean_ctor_get(v_x_2560_, 3);
v_r_2564_ = lean_ctor_get(v_x_2560_, 4);
v___x_2565_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2(v___x_2558_, v_init_2559_, v_l_2563_);
if (lean_obj_tag(v___x_2565_) == 0)
{
return v___x_2565_;
}
else
{
lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2581_; 
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2581_ == 0)
{
lean_object* v_unused_2582_; 
v_unused_2582_ = lean_ctor_get(v___x_2565_, 0);
lean_dec(v_unused_2582_);
v___x_2567_ = v___x_2565_;
v_isShared_2568_ = v_isSharedCheck_2581_;
goto v_resetjp_2566_;
}
else
{
lean_dec(v___x_2565_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2581_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2569_ = lean_box(0);
v___x_2570_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___redArg(v___x_2558_, v_k_2561_);
lean_inc(v_v_2562_);
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_v_2562_);
v___x_2572_ = l_Option_instBEq_beq___at___00Lean_Level_isEquiv_x27_spec__1(v___x_2570_, v___x_2571_);
lean_dec_ref(v___x_2571_);
lean_dec(v___x_2570_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2577_; 
v___x_2573_ = lean_box(v___x_2572_);
v___x_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v___x_2574_);
lean_ctor_set(v___x_2575_, 1, v___x_2569_);
if (v_isShared_2568_ == 0)
{
lean_ctor_set_tag(v___x_2567_, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2575_);
v___x_2577_ = v___x_2567_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v___x_2575_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
else
{
lean_object* v___x_2579_; 
lean_del_object(v___x_2567_);
v___x_2579_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v_init_2559_ = v___x_2579_;
v_x_2560_ = v_r_2564_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_init_2559_);
return v___x_2583_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2___boxed(lean_object* v___x_2584_, lean_object* v_init_2585_, lean_object* v_x_2586_){
_start:
{
lean_object* v_res_2587_; 
v_res_2587_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2(v___x_2584_, v_init_2585_, v_x_2586_);
lean_dec(v_x_2586_);
lean_dec(v___x_2584_);
return v_res_2587_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquiv_x27(lean_object* v_u_2588_, lean_object* v_v_2589_){
_start:
{
lean_object* v___y_2591_; uint8_t v___x_2596_; 
v___x_2596_ = lean_level_eq(v_u_2588_, v_v_2589_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___y_2604_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v_a_2611_; 
v___x_2597_ = l_Lean_Level_Normalize_normalize(v_u_2588_, v___x_2596_);
v___x_2598_ = l_Lean_Level_Normalize_normalize(v_v_2589_, v___x_2596_);
v___x_2609_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___x_2610_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2(v___x_2598_, v___x_2609_, v___x_2597_);
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc(v_a_2611_);
lean_dec_ref(v___x_2610_);
v___y_2604_ = v_a_2611_;
goto v___jp_2603_;
v___jp_2599_:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_a_2602_; 
v___x_2600_ = ((lean_object*)(l_Lean_Level_Normalize_instBEqNormLevel___lam__2___closed__1));
v___x_2601_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Level_isEquiv_x27_spec__2(v___x_2597_, v___x_2600_, v___x_2598_);
lean_dec(v___x_2598_);
lean_dec(v___x_2597_);
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_a_2602_);
lean_dec_ref(v___x_2601_);
v___y_2591_ = v_a_2602_;
goto v___jp_2590_;
}
v___jp_2603_:
{
lean_object* v_fst_2605_; 
v_fst_2605_ = lean_ctor_get(v___y_2604_, 0);
lean_inc(v_fst_2605_);
lean_dec_ref(v___y_2604_);
if (lean_obj_tag(v_fst_2605_) == 0)
{
goto v___jp_2599_;
}
else
{
lean_object* v_val_2606_; uint8_t v___x_2607_; 
v_val_2606_ = lean_ctor_get(v_fst_2605_, 0);
lean_inc(v_val_2606_);
lean_dec_ref(v_fst_2605_);
v___x_2607_ = lean_unbox(v_val_2606_);
if (v___x_2607_ == 0)
{
uint8_t v___x_2608_; 
lean_dec(v___x_2598_);
lean_dec(v___x_2597_);
v___x_2608_ = lean_unbox(v_val_2606_);
lean_dec(v_val_2606_);
return v___x_2608_;
}
else
{
lean_dec(v_val_2606_);
goto v___jp_2599_;
}
}
}
}
else
{
lean_dec(v_v_2589_);
lean_dec(v_u_2588_);
return v___x_2596_;
}
v___jp_2590_:
{
lean_object* v_fst_2592_; 
v_fst_2592_ = lean_ctor_get(v___y_2591_, 0);
lean_inc(v_fst_2592_);
lean_dec_ref(v___y_2591_);
if (lean_obj_tag(v_fst_2592_) == 0)
{
uint8_t v___x_2593_; 
v___x_2593_ = 1;
return v___x_2593_;
}
else
{
lean_object* v_val_2594_; uint8_t v___x_2595_; 
v_val_2594_ = lean_ctor_get(v_fst_2592_, 0);
lean_inc(v_val_2594_);
lean_dec_ref(v_fst_2592_);
v___x_2595_ = lean_unbox(v_val_2594_);
lean_dec(v_val_2594_);
return v___x_2595_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquiv_x27___boxed(lean_object* v_u_2612_, lean_object* v_v_2613_){
_start:
{
uint8_t v_res_2614_; lean_object* v_r_2615_; 
v_res_2614_ = l_Lean_Level_isEquiv_x27(v_u_2612_, v_v_2613_);
v_r_2615_ = lean_box(v_res_2614_);
return v_r_2615_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0(lean_object* v_00_u03b4_2616_, lean_object* v_t_2617_, lean_object* v_k_2618_){
_start:
{
lean_object* v___x_2619_; 
v___x_2619_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___redArg(v_t_2617_, v_k_2618_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0___boxed(lean_object* v_00_u03b4_2620_, lean_object* v_t_2621_, lean_object* v_k_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Level_isEquiv_x27_spec__0(v_00_u03b4_2620_, v_t_2621_, v_k_2622_);
lean_dec(v_k_2622_);
lean_dec(v_t_2621_);
return v_res_2623_;
}
}
LEAN_EXPORT uint8_t l_List_all2___at___00Lean_Level_isEquivList_spec__0(lean_object* v_x_2624_, lean_object* v_x_2625_){
_start:
{
if (lean_obj_tag(v_x_2624_) == 0)
{
if (lean_obj_tag(v_x_2625_) == 0)
{
uint8_t v___x_2626_; 
v___x_2626_ = 1;
return v___x_2626_;
}
else
{
uint8_t v___x_2627_; 
lean_dec_ref(v_x_2625_);
v___x_2627_ = 0;
return v___x_2627_;
}
}
else
{
if (lean_obj_tag(v_x_2625_) == 0)
{
uint8_t v___x_2628_; 
lean_dec_ref(v_x_2624_);
v___x_2628_ = 0;
return v___x_2628_;
}
else
{
lean_object* v_head_2629_; lean_object* v_tail_2630_; lean_object* v_head_2631_; lean_object* v_tail_2632_; uint8_t v___x_2633_; 
v_head_2629_ = lean_ctor_get(v_x_2624_, 0);
lean_inc(v_head_2629_);
v_tail_2630_ = lean_ctor_get(v_x_2624_, 1);
lean_inc(v_tail_2630_);
lean_dec_ref(v_x_2624_);
v_head_2631_ = lean_ctor_get(v_x_2625_, 0);
lean_inc(v_head_2631_);
v_tail_2632_ = lean_ctor_get(v_x_2625_, 1);
lean_inc(v_tail_2632_);
lean_dec_ref(v_x_2625_);
v___x_2633_ = l_Lean_Level_isEquiv_x27(v_head_2629_, v_head_2631_);
if (v___x_2633_ == 0)
{
lean_dec(v_tail_2632_);
lean_dec(v_tail_2630_);
return v___x_2633_;
}
else
{
v_x_2624_ = v_tail_2630_;
v_x_2625_ = v_tail_2632_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all2___at___00Lean_Level_isEquivList_spec__0___boxed(lean_object* v_x_2635_, lean_object* v_x_2636_){
_start:
{
uint8_t v_res_2637_; lean_object* v_r_2638_; 
v_res_2637_ = l_List_all2___at___00Lean_Level_isEquivList_spec__0(v_x_2635_, v_x_2636_);
v_r_2638_ = lean_box(v_res_2637_);
return v_r_2638_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_isEquivList(lean_object* v_a_2639_, lean_object* v_a_2640_){
_start:
{
uint8_t v___x_2641_; 
v___x_2641_ = l_List_all2___at___00Lean_Level_isEquivList_spec__0(v_a_2639_, v_a_2640_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_isEquivList___boxed(lean_object* v_a_2642_, lean_object* v_a_2643_){
_start:
{
uint8_t v_res_2644_; lean_object* v_r_2645_; 
v_res_2644_ = l_Lean_Level_isEquivList(v_a_2642_, v_a_2643_);
v_r_2645_ = lean_box(v_res_2644_);
return v_r_2645_;
}
}
LEAN_EXPORT uint8_t l_Lean_Level_geq_x27(lean_object* v_u_2646_, lean_object* v_v_2647_){
_start:
{
uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; uint8_t v___x_2651_; 
v___x_2648_ = 0;
v___x_2649_ = l_Lean_Level_Normalize_normalize(v_v_2647_, v___x_2648_);
v___x_2650_ = l_Lean_Level_Normalize_normalize(v_u_2646_, v___x_2648_);
v___x_2651_ = l_Lean_Level_Normalize_NormLevel_le(v___x_2649_, v___x_2650_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Level_geq_x27___boxed(lean_object* v_u_2652_, lean_object* v_v_2653_){
_start:
{
uint8_t v_res_2654_; lean_object* v_r_2655_; 
v_res_2654_ = l_Lean_Level_geq_x27(v_u_2652_, v_v_2653_);
v_r_2655_ = lean_box(v_res_2654_);
return v_r_2655_;
}
}
lean_object* runtime_initialize_Lean(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_List(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Level(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Level(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean(uint8_t builtin);
lean_object* initialize_Lean_Kernel_List(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Level(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Level(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Level(builtin);
}
#ifdef __cplusplus
}
#endif
