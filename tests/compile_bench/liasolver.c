// Lean compiler output
// Module: liasolver
// Imports: public import Init public meta import Init public import Lean.Data.AssocList public import Std.Data.HashMap public import Std.Data.Iterators.Producers.Range public import Std.Data.Iterators.Combinators.StepSize
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_length___redArg(lean_object*);
lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___redArg(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Int_repr(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_String_Slice_toInt_x3f(lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_natAbs___boxed(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_IO_FS_lines___boxed(lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_get_stdout();
lean_object* lean_array_to_list(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
static lean_once_cell_t l_Int_roundedDiv___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_roundedDiv___closed__0;
static lean_once_cell_t l_Int_roundedDiv___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_roundedDiv___closed__1;
static lean_once_cell_t l_Int_roundedDiv___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_roundedDiv___closed__2;
static lean_once_cell_t l_Int_roundedDiv___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Int_roundedDiv___closed__3;
LEAN_EXPORT lean_object* l_Int_roundedDiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_roundedDiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_mod_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_mod_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_map___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_filter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_AssocList_filter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_mapVals___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_mapVals___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__1_value;
static const lean_closure_object l_Std_HashMap_mapVals___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__2 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__2_value;
static const lean_closure_object l_Std_HashMap_mapVals___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__3 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__3_value;
static const lean_closure_object l_Std_HashMap_mapVals___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__4 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__4_value;
static const lean_closure_object l_Std_HashMap_mapVals___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__5 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__5_value;
static const lean_closure_object l_Std_HashMap_mapVals___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__6 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__6_value;
static const lean_ctor_object l_Std_HashMap_mapVals___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__0_value),((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__1_value)}};
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__7 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__7_value;
static const lean_ctor_object l_Std_HashMap_mapVals___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__7_value),((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__2_value),((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__3_value),((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__4_value),((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__5_value)}};
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__8 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__8_value;
static const lean_ctor_object l_Std_HashMap_mapVals___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__8_value),((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__6_value)}};
static const lean_object* l_Std_HashMap_mapVals___redArg___closed__9 = (const lean_object*)&l_Std_HashMap_mapVals___redArg___closed__9_value;
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_HashMap_getAny_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_getAny_x3f___redArg___lam__0___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Std_HashMap_getAny_x3f___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_getAny_x3f___redArg___closed__0_value;
static const lean_closure_object l_Std_HashMap_getAny_x3f___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_HashMap_getAny_x3f___redArg___lam__1, .m_arity = 5, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Std_HashMap_mapVals___redArg___closed__9_value),((lean_object*)&l_Std_HashMap_getAny_x3f___redArg___closed__0_value)} };
static const lean_object* l_Std_HashMap_getAny_x3f___redArg___closed__1 = (const lean_object*)&l_Std_HashMap_getAny_x3f___redArg___closed__1_value;
static const lean_ctor_object l_Std_HashMap_getAny_x3f___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_getAny_x3f___redArg___closed__2 = (const lean_object*)&l_Std_HashMap_getAny_x3f___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_instInhabitedEquation_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instInhabitedEquation_default___closed__0;
static lean_once_cell_t l_instInhabitedEquation_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instInhabitedEquation_default___closed__1;
static lean_once_cell_t l_instInhabitedEquation_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instInhabitedEquation_default___closed__2;
LEAN_EXPORT lean_object* l_instInhabitedEquation_default;
LEAN_EXPORT lean_object* l_instInhabitedEquation;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___at___00gcd_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_gcd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Int_natAbs___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_gcd___closed__0 = (const lean_object*)&l_gcd___closed__0_value;
static const lean_ctor_object l_gcd___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_gcd___closed__1 = (const lean_object*)&l_gcd___closed__1_value;
static const lean_string_object l_gcd___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "liasolver"};
static const lean_object* l_gcd___closed__2 = (const lean_object*)&l_gcd___closed__2_value;
static const lean_string_object l_gcd___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "gcd"};
static const lean_object* l_gcd___closed__3 = (const lean_object*)&l_gcd___closed__3_value;
static const lean_string_object l_gcd___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Cannot calculate GCD of empty list of coefficients"};
static const lean_object* l_gcd___closed__4 = (const lean_object*)&l_gcd___closed__4_value;
static lean_once_cell_t l_gcd___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_gcd___closed__5;
LEAN_EXPORT lean_object* l_gcd(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___at___00gcd_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_preprocess_x3f___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_preprocess_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_preprocess_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_subst___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_subst___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_subst_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_subst_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_subst_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_subst_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__7(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__8(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0_spec__1(lean_object*);
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Std.Data.DHashMap.Internal.AssocList.Basic"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__0 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__0_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "Std.DHashMap.Internal.AssocList.get!"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__1 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__1_value;
static const lean_string_object l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "key is not present in hash table"};
static const lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__2 = (const lean_object*)&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__2_value;
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_subst(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_subst___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Equation_normalize_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Equation_normalize_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Equation_normalize_spec__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg___closed__0 = (const lean_object*)&l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg___boxed(lean_object*);
static const lean_string_object l_Equation_normalize___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Equation_normalize___closed__0 = (const lean_object*)&l_Equation_normalize___closed__0_value;
static const lean_string_object l_Equation_normalize___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Equation_normalize___closed__1 = (const lean_object*)&l_Equation_normalize___closed__1_value;
static const lean_string_object l_Equation_normalize___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Equation_normalize___closed__2 = (const lean_object*)&l_Equation_normalize___closed__2_value;
static lean_once_cell_t l_Equation_normalize___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Equation_normalize___closed__3;
LEAN_EXPORT lean_object* l_Equation_normalize(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_invert___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_invert___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Equation_invert___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Equation_invert___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Equation_invert___closed__0 = (const lean_object*)&l_Equation_invert___closed__0_value;
LEAN_EXPORT lean_object* l_Equation_invert(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_reorganizeFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_reorganizeFor___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findSingleton_x3f_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findSingleton_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_findSingleton_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Equation_findSingleton_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findAbsMinimumCoeff_x3f_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findAbsMinimumCoeff_x3f_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findAbsMinimumCoeff_x3f_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findAbsMinimumCoeff_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Equation_findAbsMinimumCoeff_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Equation_findAbsMinimumCoeff_x3f___boxed(lean_object*);
static lean_once_cell_t l_instInhabitedProblem_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_instInhabitedProblem_default___closed__0;
LEAN_EXPORT lean_object* l_instInhabitedProblem_default;
LEAN_EXPORT lean_object* l_instInhabitedProblem;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0___redArg(lean_object*, lean_object*);
static const lean_closure_object l_preprocess_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Equation_preprocess_x3f, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_preprocess_x3f___closed__0 = (const lean_object*)&l_preprocess_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_preprocess_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingleton_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingleton_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1_spec__5(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_eliminateSingleton___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_eliminateSingleton___closed__0 = (const lean_object*)&l_eliminateSingleton___closed__0_value;
LEAN_EXPORT lean_object* l_eliminateSingleton(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingletons_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingletons_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingletons_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingletons_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_eliminateSingletons(lean_object*);
LEAN_EXPORT lean_object* l_addAuxEquation___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_addAuxEquation___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_addAuxEquation___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_addAuxEquation___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__6(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00addAuxEquation_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00addAuxEquation_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00addAuxEquation_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00addAuxEquation_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_addAuxEquation___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_addAuxEquation___closed__0 = (const lean_object*)&l_addAuxEquation___closed__0_value;
static const lean_ctor_object l_addAuxEquation___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_addAuxEquation___closed__0_value)}};
static const lean_object* l_addAuxEquation___closed__1 = (const lean_object*)&l_addAuxEquation___closed__1_value;
LEAN_EXPORT lean_object* l_addAuxEquation(lean_object*);
LEAN_EXPORT lean_object* l_Solution_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Solution_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Solution_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solution_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solution_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solution_unsat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solution_unsat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solution_sat_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Solution_sat_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instInhabitedSolution_default;
LEAN_EXPORT lean_object* l_instInhabitedSolution;
static lean_once_cell_t l_readSolution_x3f_readSolution___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_readSolution_x3f_readSolution___closed__0;
LEAN_EXPORT lean_object* l_readSolution_x3f_readSolution(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_readSolution_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_readSolution_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_readSolution_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_readSolution_x3f_readSolution___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_readSolution_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__0 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__0_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__1 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__1_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__1_value)}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__2 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__2_value;
static const lean_ctor_object l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3 = (const lean_object*)&l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3_value;
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00readSolution_x3f_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00readSolution_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_readSolution_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_readSolution_x3f___closed__0 = (const lean_object*)&l_readSolution_x3f___closed__0_value;
LEAN_EXPORT lean_object* l_readSolution_x3f(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_solveProblem_x27(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_isSatAssignment(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_isSatAssignment___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_solveProblem(lean_object*);
static const lean_string_object l_error___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Error: "};
static const lean_object* l_error___redArg___closed__0 = (const lean_object*)&l_error___redArg___closed__0_value;
static const lean_string_object l_error___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_error___redArg___closed__1 = (const lean_object*)&l_error___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_error___redArg(lean_object*);
LEAN_EXPORT lean_object* l_error___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_error(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_error___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Array_ithVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Missing "};
static const lean_object* l_Array_ithVal___closed__0 = (const lean_object*)&l_Array_ithVal___closed__0_value;
static const lean_string_object l_Array_ithVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Invalid "};
static const lean_object* l_Array_ithVal___closed__1 = (const lean_object*)&l_Array_ithVal___closed__1_value;
static const lean_string_object l_Array_ithVal___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ": `"};
static const lean_object* l_Array_ithVal___closed__2 = (const lean_object*)&l_Array_ithVal___closed__2_value;
static const lean_string_object l_Array_ithVal___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Array_ithVal___closed__3 = (const lean_object*)&l_Array_ithVal___closed__3_value;
LEAN_EXPORT lean_object* l_Array_ithVal(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_ithVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_main___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_main___lam__0___closed__0 = (const lean_object*)&l_main___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_main___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "coefficient"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "variable index"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Invalid variable index"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__0_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "amount of equation terms"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__1 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__1_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "end of line symbol"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__2_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Non-zero end of line symbol"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__3 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__3_value;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "constant value"};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__4_value;
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__5 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__5_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__1_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00main_spec__5(lean_object*, lean_object*);
static const lean_closure_object l_main___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_main___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_main___closed__0 = (const lean_object*)&l_main___closed__0_value;
static const lean_string_object l_main___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "No header line"};
static const lean_object* l_main___closed__1 = (const lean_object*)&l_main___closed__1_value;
static const lean_string_object l_main___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "amount of equations"};
static const lean_object* l_main___closed__2 = (const lean_object*)&l_main___closed__2_value;
static const lean_string_object l_main___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "amount of variables"};
static const lean_object* l_main___closed__3 = (const lean_object*)&l_main___closed__3_value;
static const lean_string_object l_main___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "UNSAT"};
static const lean_object* l_main___closed__4 = (const lean_object*)&l_main___closed__4_value;
static const lean_string_object l_main___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "SAT"};
static const lean_object* l_main___closed__5 = (const lean_object*)&l_main___closed__5_value;
static const lean_string_object l_main___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Usage: liasolver <input file>"};
static const lean_object* l_main___closed__6 = (const lean_object*)&l_main___closed__6_value;
LEAN_EXPORT lean_object* l_main___boxed__const__1;
LEAN_EXPORT lean_object* _lean_main(lean_object*);
LEAN_EXPORT lean_object* l_main___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Int_roundedDiv___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(0u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
static lean_object* _init_l_Int_roundedDiv___closed__1(void){
_start:
{
lean_object* v___x_3_; lean_object* v___x_4_; 
v___x_3_ = lean_unsigned_to_nat(2u);
v___x_4_ = lean_nat_to_int(v___x_3_);
return v___x_4_;
}
}
static lean_object* _init_l_Int_roundedDiv___closed__2(void){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_unsigned_to_nat(1u);
v___x_6_ = lean_nat_to_int(v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Int_roundedDiv___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_7_ = lean_obj_once(&l_Int_roundedDiv___closed__2, &l_Int_roundedDiv___closed__2_once, _init_l_Int_roundedDiv___closed__2);
v___x_8_ = lean_int_neg(v___x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Int_roundedDiv(lean_object* v_a_9_, lean_object* v_b_10_){
_start:
{
lean_object* v___x_11_; uint8_t v___x_12_; 
v___x_11_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_12_ = lean_int_dec_eq(v_b_10_, v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v_div_13_; lean_object* v_rest_14_; uint8_t v___x_15_; 
v_div_13_ = lean_int_ediv(v_a_9_, v_b_10_);
v_rest_14_ = lean_int_emod(v_a_9_, v_b_10_);
v___x_15_ = lean_int_dec_le(v___x_11_, v_a_9_);
if (v___x_15_ == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_16_ = lean_nat_abs(v_b_10_);
v___x_17_ = lean_nat_to_int(v___x_16_);
v___x_18_ = lean_obj_once(&l_Int_roundedDiv___closed__1, &l_Int_roundedDiv___closed__1_once, _init_l_Int_roundedDiv___closed__1);
v___x_19_ = lean_int_mul(v___x_18_, v_rest_14_);
lean_dec(v_rest_14_);
v___x_20_ = lean_int_dec_lt(v___x_17_, v___x_19_);
lean_dec(v___x_19_);
lean_dec(v___x_17_);
if (v___x_20_ == 0)
{
return v_div_13_;
}
else
{
uint8_t v___x_21_; 
v___x_21_ = lean_int_dec_le(v___x_11_, v_b_10_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v_div_23_; 
v___x_22_ = lean_obj_once(&l_Int_roundedDiv___closed__3, &l_Int_roundedDiv___closed__3_once, _init_l_Int_roundedDiv___closed__3);
v_div_23_ = lean_int_add(v_div_13_, v___x_22_);
lean_dec(v_div_13_);
return v_div_23_;
}
else
{
lean_object* v___x_24_; lean_object* v_div_25_; 
v___x_24_ = lean_obj_once(&l_Int_roundedDiv___closed__2, &l_Int_roundedDiv___closed__2_once, _init_l_Int_roundedDiv___closed__2);
v_div_25_ = lean_int_add(v_div_13_, v___x_24_);
lean_dec(v_div_13_);
return v_div_25_;
}
}
}
else
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; uint8_t v___x_30_; 
v___x_26_ = lean_nat_abs(v_b_10_);
v___x_27_ = lean_nat_to_int(v___x_26_);
v___x_28_ = lean_obj_once(&l_Int_roundedDiv___closed__1, &l_Int_roundedDiv___closed__1_once, _init_l_Int_roundedDiv___closed__1);
v___x_29_ = lean_int_mul(v___x_28_, v_rest_14_);
lean_dec(v_rest_14_);
v___x_30_ = lean_int_dec_le(v___x_27_, v___x_29_);
lean_dec(v___x_29_);
lean_dec(v___x_27_);
if (v___x_30_ == 0)
{
return v_div_13_;
}
else
{
uint8_t v___x_31_; 
v___x_31_ = lean_int_dec_le(v___x_11_, v_b_10_);
if (v___x_31_ == 0)
{
lean_object* v___x_32_; lean_object* v_div_33_; 
v___x_32_ = lean_obj_once(&l_Int_roundedDiv___closed__3, &l_Int_roundedDiv___closed__3_once, _init_l_Int_roundedDiv___closed__3);
v_div_33_ = lean_int_add(v_div_13_, v___x_32_);
lean_dec(v_div_13_);
return v_div_33_;
}
else
{
lean_object* v___x_34_; lean_object* v_div_35_; 
v___x_34_ = lean_obj_once(&l_Int_roundedDiv___closed__2, &l_Int_roundedDiv___closed__2_once, _init_l_Int_roundedDiv___closed__2);
v_div_35_ = lean_int_add(v_div_13_, v___x_34_);
lean_dec(v_div_13_);
return v_div_35_;
}
}
}
}
else
{
return v___x_11_;
}
}
}
LEAN_EXPORT lean_object* l_Int_roundedDiv___boxed(lean_object* v_a_36_, lean_object* v_b_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Int_roundedDiv(v_a_36_, v_b_37_);
lean_dec(v_b_37_);
lean_dec(v_a_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Int_mod_x27(lean_object* v_a_39_, lean_object* v_b_40_){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_41_ = l_Int_roundedDiv(v_a_39_, v_b_40_);
v___x_42_ = lean_int_mul(v_b_40_, v___x_41_);
lean_dec(v___x_41_);
v___x_43_ = lean_int_sub(v_a_39_, v___x_42_);
lean_dec(v___x_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Int_mod_x27___boxed(lean_object* v_a_44_, lean_object* v_b_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Int_mod_x27(v_a_44_, v_b_45_);
lean_dec(v_b_45_);
lean_dec(v_a_44_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_map___redArg(lean_object* v_f_47_, lean_object* v_x_48_){
_start:
{
if (lean_obj_tag(v_x_48_) == 0)
{
lean_object* v___x_49_; 
lean_dec(v_f_47_);
v___x_49_ = lean_box(0);
return v___x_49_;
}
else
{
lean_object* v_key_50_; lean_object* v_value_51_; lean_object* v_tail_52_; lean_object* v___x_54_; uint8_t v_isShared_55_; uint8_t v_isSharedCheck_61_; 
v_key_50_ = lean_ctor_get(v_x_48_, 0);
v_value_51_ = lean_ctor_get(v_x_48_, 1);
v_tail_52_ = lean_ctor_get(v_x_48_, 2);
v_isSharedCheck_61_ = !lean_is_exclusive(v_x_48_);
if (v_isSharedCheck_61_ == 0)
{
v___x_54_ = v_x_48_;
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
else
{
lean_inc(v_tail_52_);
lean_inc(v_value_51_);
lean_inc(v_key_50_);
lean_dec(v_x_48_);
v___x_54_ = lean_box(0);
v_isShared_55_ = v_isSharedCheck_61_;
goto v_resetjp_53_;
}
v_resetjp_53_:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_59_; 
lean_inc(v_f_47_);
lean_inc(v_key_50_);
v___x_56_ = lean_apply_2(v_f_47_, v_key_50_, v_value_51_);
v___x_57_ = l_Lean_AssocList_map___redArg(v_f_47_, v_tail_52_);
if (v_isShared_55_ == 0)
{
lean_ctor_set(v___x_54_, 2, v___x_57_);
lean_ctor_set(v___x_54_, 1, v___x_56_);
v___x_59_ = v___x_54_;
goto v_reusejp_58_;
}
else
{
lean_object* v_reuseFailAlloc_60_; 
v_reuseFailAlloc_60_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_60_, 0, v_key_50_);
lean_ctor_set(v_reuseFailAlloc_60_, 1, v___x_56_);
lean_ctor_set(v_reuseFailAlloc_60_, 2, v___x_57_);
v___x_59_ = v_reuseFailAlloc_60_;
goto v_reusejp_58_;
}
v_reusejp_58_:
{
return v___x_59_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_map(lean_object* v_00_u03b1_62_, lean_object* v_00_u03b2_63_, lean_object* v_00_u03b4_64_, lean_object* v_f_65_, lean_object* v_x_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = l_Lean_AssocList_map___redArg(v_f_65_, v_x_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_filter___redArg(lean_object* v_p_68_, lean_object* v_x_69_){
_start:
{
if (lean_obj_tag(v_x_69_) == 0)
{
lean_dec_ref(v_p_68_);
return v_x_69_;
}
else
{
lean_object* v_key_70_; lean_object* v_value_71_; lean_object* v_tail_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_83_; 
v_key_70_ = lean_ctor_get(v_x_69_, 0);
v_value_71_ = lean_ctor_get(v_x_69_, 1);
v_tail_72_ = lean_ctor_get(v_x_69_, 2);
v_isSharedCheck_83_ = !lean_is_exclusive(v_x_69_);
if (v_isSharedCheck_83_ == 0)
{
v___x_74_ = v_x_69_;
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_tail_72_);
lean_inc(v_value_71_);
lean_inc(v_key_70_);
lean_dec(v_x_69_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; uint8_t v___x_77_; 
lean_inc_ref(v_p_68_);
lean_inc(v_value_71_);
lean_inc(v_key_70_);
v___x_76_ = lean_apply_2(v_p_68_, v_key_70_, v_value_71_);
v___x_77_ = lean_unbox(v___x_76_);
if (v___x_77_ == 0)
{
lean_del_object(v___x_74_);
lean_dec(v_value_71_);
lean_dec(v_key_70_);
v_x_69_ = v_tail_72_;
goto _start;
}
else
{
lean_object* v___x_79_; lean_object* v___x_81_; 
v___x_79_ = l_Lean_AssocList_filter___redArg(v_p_68_, v_tail_72_);
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 2, v___x_79_);
v___x_81_ = v___x_74_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_key_70_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_value_71_);
lean_ctor_set(v_reuseFailAlloc_82_, 2, v___x_79_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
return v___x_81_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_AssocList_filter(lean_object* v_00_u03b1_84_, lean_object* v_00_u03b2_85_, lean_object* v_p_86_, lean_object* v_x_87_){
_start:
{
lean_object* v___x_88_; 
v___x_88_ = l_Lean_AssocList_filter___redArg(v_p_86_, v_x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___redArg(lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_inst_91_, lean_object* v_xs_92_, lean_object* v_k_93_, lean_object* v_f_94_){
_start:
{
lean_object* v_v_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
lean_inc_n(v_k_93_, 2);
lean_inc_ref_n(v_inst_90_, 2);
lean_inc_ref_n(v_inst_89_, 2);
v_v_95_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___redArg(v_inst_89_, v_inst_90_, v_inst_91_, v_xs_92_, v_k_93_);
v___x_96_ = l_Std_DHashMap_Internal_Raw_u2080_erase___redArg(v_inst_89_, v_inst_90_, v_xs_92_, v_k_93_);
v___x_97_ = lean_apply_1(v_f_94_, v_v_95_);
v___x_98_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_89_, v_inst_90_, v___x_96_, v_k_93_, v___x_97_);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___redArg___boxed(lean_object* v_inst_99_, lean_object* v_inst_100_, lean_object* v_inst_101_, lean_object* v_xs_102_, lean_object* v_k_103_, lean_object* v_f_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Std_HashMap_modify_x21___redArg(v_inst_99_, v_inst_100_, v_inst_101_, v_xs_102_, v_k_103_, v_f_104_);
lean_dec(v_inst_101_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21(lean_object* v_00_u03b1_106_, lean_object* v_inst_107_, lean_object* v_inst_108_, lean_object* v_00_u03b2_109_, lean_object* v_inst_110_, lean_object* v_xs_111_, lean_object* v_k_112_, lean_object* v_f_113_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Std_HashMap_modify_x21___redArg(v_inst_107_, v_inst_108_, v_inst_110_, v_xs_111_, v_k_112_, v_f_113_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___boxed(lean_object* v_00_u03b1_115_, lean_object* v_inst_116_, lean_object* v_inst_117_, lean_object* v_00_u03b2_118_, lean_object* v_inst_119_, lean_object* v_xs_120_, lean_object* v_k_121_, lean_object* v_f_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_HashMap_modify_x21(v_00_u03b1_115_, v_inst_116_, v_inst_117_, v_00_u03b2_118_, v_inst_119_, v_xs_120_, v_k_121_, v_f_122_);
lean_dec(v_inst_119_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg___lam__0(lean_object* v_inst_124_, lean_object* v_inst_125_, lean_object* v_acc_126_, lean_object* v_k_127_, lean_object* v_toPure_128_, lean_object* v_____do__lift_129_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_130_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_124_, v_inst_125_, v_acc_126_, v_k_127_, v_____do__lift_129_);
v___x_131_ = lean_apply_2(v_toPure_128_, lean_box(0), v___x_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg___lam__1(lean_object* v_inst_132_, lean_object* v_inst_133_, lean_object* v_toPure_134_, lean_object* v_f_135_, lean_object* v_toBind_136_, lean_object* v_acc_137_, lean_object* v_k_138_, lean_object* v_v_139_){
_start:
{
lean_object* v___f_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v___f_140_ = lean_alloc_closure((void*)(l_Std_HashMap_mapValsM___redArg___lam__0), 6, 5);
lean_closure_set(v___f_140_, 0, v_inst_132_);
lean_closure_set(v___f_140_, 1, v_inst_133_);
lean_closure_set(v___f_140_, 2, v_acc_137_);
lean_closure_set(v___f_140_, 3, v_k_138_);
lean_closure_set(v___f_140_, 4, v_toPure_134_);
v___x_141_ = lean_apply_1(v_f_135_, v_v_139_);
v___x_142_ = lean_apply_4(v_toBind_136_, lean_box(0), lean_box(0), v___x_141_, v___f_140_);
return v___x_142_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg___lam__2(lean_object* v_inst_143_, lean_object* v___f_144_, lean_object* v_acc_145_, lean_object* v_l_146_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v_inst_143_, v___f_144_, v_acc_145_, v_l_146_);
return v___x_147_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___redArg(lean_object* v_inst_148_, lean_object* v_inst_149_, lean_object* v_inst_150_, lean_object* v_f_151_, lean_object* v_xs_152_){
_start:
{
lean_object* v_toApplicative_153_; lean_object* v_toBind_154_; lean_object* v_toPure_155_; lean_object* v_size_156_; lean_object* v_buckets_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_185_; 
v_toApplicative_153_ = lean_ctor_get(v_inst_150_, 0);
v_toBind_154_ = lean_ctor_get(v_inst_150_, 1);
v_toPure_155_ = lean_ctor_get(v_toApplicative_153_, 1);
v_size_156_ = lean_ctor_get(v_xs_152_, 0);
v_buckets_157_ = lean_ctor_get(v_xs_152_, 1);
v_isSharedCheck_185_ = !lean_is_exclusive(v_xs_152_);
if (v_isSharedCheck_185_ == 0)
{
v___x_159_ = v_xs_152_;
v_isShared_160_ = v_isSharedCheck_185_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_buckets_157_);
lean_inc(v_size_156_);
lean_dec(v_xs_152_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_185_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_161_ = lean_unsigned_to_nat(0u);
v___x_162_ = lean_unsigned_to_nat(4u);
v___x_163_ = lean_nat_mul(v_size_156_, v___x_162_);
lean_dec(v_size_156_);
v___x_164_ = lean_unsigned_to_nat(3u);
v___x_165_ = lean_nat_div(v___x_163_, v___x_164_);
lean_dec(v___x_163_);
v___x_166_ = l_Nat_nextPowerOfTwo(v___x_165_);
lean_dec(v___x_165_);
v___x_167_ = lean_box(0);
v___x_168_ = lean_mk_array(v___x_166_, v___x_167_);
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 1, v___x_168_);
lean_ctor_set(v___x_159_, 0, v___x_161_);
v___x_170_ = v___x_159_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v___x_161_);
lean_ctor_set(v_reuseFailAlloc_184_, 1, v___x_168_);
v___x_170_ = v_reuseFailAlloc_184_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_171_ = lean_array_get_size(v_buckets_157_);
v___x_172_ = lean_nat_dec_lt(v___x_161_, v___x_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; 
lean_inc(v_toPure_155_);
lean_dec_ref(v_buckets_157_);
lean_dec(v_f_151_);
lean_dec_ref(v_inst_150_);
lean_dec_ref(v_inst_149_);
lean_dec_ref(v_inst_148_);
v___x_173_ = lean_apply_2(v_toPure_155_, lean_box(0), v___x_170_);
return v___x_173_;
}
else
{
lean_object* v___f_174_; lean_object* v___f_175_; uint8_t v___x_176_; 
lean_inc(v_toBind_154_);
lean_inc(v_toPure_155_);
v___f_174_ = lean_alloc_closure((void*)(l_Std_HashMap_mapValsM___redArg___lam__1), 8, 5);
lean_closure_set(v___f_174_, 0, v_inst_148_);
lean_closure_set(v___f_174_, 1, v_inst_149_);
lean_closure_set(v___f_174_, 2, v_toPure_155_);
lean_closure_set(v___f_174_, 3, v_f_151_);
lean_closure_set(v___f_174_, 4, v_toBind_154_);
lean_inc_ref(v_inst_150_);
v___f_175_ = lean_alloc_closure((void*)(l_Std_HashMap_mapValsM___redArg___lam__2), 4, 2);
lean_closure_set(v___f_175_, 0, v_inst_150_);
lean_closure_set(v___f_175_, 1, v___f_174_);
v___x_176_ = lean_nat_dec_le(v___x_171_, v___x_171_);
if (v___x_176_ == 0)
{
if (v___x_172_ == 0)
{
lean_object* v___x_177_; 
lean_inc(v_toPure_155_);
lean_dec_ref(v___f_175_);
lean_dec_ref(v_buckets_157_);
lean_dec_ref(v_inst_150_);
v___x_177_ = lean_apply_2(v_toPure_155_, lean_box(0), v___x_170_);
return v___x_177_;
}
else
{
size_t v___x_178_; size_t v___x_179_; lean_object* v___x_180_; 
v___x_178_ = ((size_t)0ULL);
v___x_179_ = lean_usize_of_nat(v___x_171_);
v___x_180_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_150_, v___f_175_, v_buckets_157_, v___x_178_, v___x_179_, v___x_170_);
return v___x_180_;
}
}
else
{
size_t v___x_181_; size_t v___x_182_; lean_object* v___x_183_; 
v___x_181_ = ((size_t)0ULL);
v___x_182_ = lean_usize_of_nat(v___x_171_);
v___x_183_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v_inst_150_, v___f_175_, v_buckets_157_, v___x_181_, v___x_182_, v___x_170_);
return v___x_183_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM(lean_object* v_00_u03b1_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_m_189_, lean_object* v_00_u03b2_190_, lean_object* v_00_u03b3_191_, lean_object* v_inst_192_, lean_object* v_f_193_, lean_object* v_xs_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = l_Std_HashMap_mapValsM___redArg(v_inst_187_, v_inst_188_, v_inst_192_, v_f_193_, v_xs_194_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___redArg___lam__0(lean_object* v_f_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_x1_199_, lean_object* v_x2_200_, lean_object* v_x3_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_202_ = lean_apply_1(v_f_196_, v_x3_201_);
v___x_203_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v_inst_197_, v_inst_198_, v_x1_199_, v_x2_200_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___redArg___lam__1(lean_object* v___x_204_, lean_object* v___f_205_, lean_object* v_acc_206_, lean_object* v_l_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l_Std_DHashMap_Internal_AssocList_foldlM___redArg(v___x_204_, v___f_205_, v_acc_206_, v_l_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___redArg(lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_f_230_, lean_object* v_xs_231_){
_start:
{
lean_object* v_size_232_; lean_object* v_buckets_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_260_; 
v_size_232_ = lean_ctor_get(v_xs_231_, 0);
v_buckets_233_ = lean_ctor_get(v_xs_231_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_xs_231_);
if (v_isSharedCheck_260_ == 0)
{
v___x_235_ = v_xs_231_;
v_isShared_236_ = v_isSharedCheck_260_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_buckets_233_);
lean_inc(v_size_232_);
lean_dec(v_xs_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_260_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_237_ = lean_unsigned_to_nat(0u);
v___x_238_ = lean_unsigned_to_nat(4u);
v___x_239_ = lean_nat_mul(v_size_232_, v___x_238_);
lean_dec(v_size_232_);
v___x_240_ = lean_unsigned_to_nat(3u);
v___x_241_ = lean_nat_div(v___x_239_, v___x_240_);
lean_dec(v___x_239_);
v___x_242_ = l_Nat_nextPowerOfTwo(v___x_241_);
lean_dec(v___x_241_);
v___x_243_ = lean_box(0);
v___x_244_ = lean_mk_array(v___x_242_, v___x_243_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_244_);
lean_ctor_set(v___x_235_, 0, v___x_237_);
v___x_246_ = v___x_235_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_237_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_244_);
v___x_246_ = v_reuseFailAlloc_259_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
lean_object* v___x_247_; lean_object* v___x_248_; uint8_t v___x_249_; 
v___x_247_ = ((lean_object*)(l_Std_HashMap_mapVals___redArg___closed__9));
v___x_248_ = lean_array_get_size(v_buckets_233_);
v___x_249_ = lean_nat_dec_lt(v___x_237_, v___x_248_);
if (v___x_249_ == 0)
{
lean_dec_ref(v_buckets_233_);
lean_dec(v_f_230_);
lean_dec_ref(v_inst_229_);
lean_dec_ref(v_inst_228_);
return v___x_246_;
}
else
{
lean_object* v___f_250_; lean_object* v___f_251_; uint8_t v___x_252_; 
v___f_250_ = lean_alloc_closure((void*)(l_Std_HashMap_mapVals___redArg___lam__0), 6, 3);
lean_closure_set(v___f_250_, 0, v_f_230_);
lean_closure_set(v___f_250_, 1, v_inst_228_);
lean_closure_set(v___f_250_, 2, v_inst_229_);
v___f_251_ = lean_alloc_closure((void*)(l_Std_HashMap_mapVals___redArg___lam__1), 4, 2);
lean_closure_set(v___f_251_, 0, v___x_247_);
lean_closure_set(v___f_251_, 1, v___f_250_);
v___x_252_ = lean_nat_dec_le(v___x_248_, v___x_248_);
if (v___x_252_ == 0)
{
if (v___x_249_ == 0)
{
lean_dec_ref(v___f_251_);
lean_dec_ref(v_buckets_233_);
return v___x_246_;
}
else
{
size_t v___x_253_; size_t v___x_254_; lean_object* v___x_255_; 
v___x_253_ = ((size_t)0ULL);
v___x_254_ = lean_usize_of_nat(v___x_248_);
v___x_255_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_247_, v___f_251_, v_buckets_233_, v___x_253_, v___x_254_, v___x_246_);
return v___x_255_;
}
}
else
{
size_t v___x_256_; size_t v___x_257_; lean_object* v___x_258_; 
v___x_256_ = ((size_t)0ULL);
v___x_257_ = lean_usize_of_nat(v___x_248_);
v___x_258_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___redArg(v___x_247_, v___f_251_, v_buckets_233_, v___x_256_, v___x_257_, v___x_246_);
return v___x_258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals(lean_object* v_00_u03b1_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_00_u03b2_264_, lean_object* v_00_u03b3_265_, lean_object* v_f_266_, lean_object* v_xs_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_HashMap_mapVals___redArg(v_inst_262_, v_inst_263_, v_f_266_, v_xs_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___redArg(lean_object* v_f_269_, lean_object* v_xs_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_269_, v_xs_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals(lean_object* v_00_u03b1_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_00_u03b2_275_, lean_object* v_f_276_, lean_object* v_xs_277_){
_start:
{
lean_object* v___x_278_; 
v___x_278_ = l_Std_DHashMap_Internal_Raw_u2080_map___redArg(v_f_276_, v_xs_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___boxed(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_00_u03b2_282_, lean_object* v_f_283_, lean_object* v_xs_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_HashMap_fastMapVals(v_00_u03b1_279_, v_inst_280_, v_inst_281_, v_00_u03b2_282_, v_f_283_, v_xs_284_);
lean_dec_ref(v_inst_281_);
lean_dec_ref(v_inst_280_);
return v_res_285_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg___lam__0(lean_object* v___x_286_, lean_object* v_a_287_, lean_object* v_b_288_, lean_object* v_acc_289_){
_start:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; 
v___x_290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_290_, 0, v_a_287_);
lean_ctor_set(v___x_290_, 1, v_b_288_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v___x_291_);
v___x_293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_293_, 0, v___x_292_);
lean_ctor_set(v___x_293_, 1, v___x_286_);
v___x_294_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_294_, 0, v___x_293_);
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg___lam__0___boxed(lean_object* v___x_295_, lean_object* v_a_296_, lean_object* v_b_297_, lean_object* v_acc_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Std_HashMap_getAny_x3f___redArg___lam__0(v___x_295_, v_a_296_, v_b_297_, v_acc_298_);
lean_dec_ref(v_acc_298_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg___lam__1(lean_object* v___x_300_, lean_object* v___f_301_, lean_object* v_a_302_, lean_object* v_x_303_, lean_object* v___y_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___redArg(v___x_300_, v___f_301_, v_a_302_, v___y_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___redArg(lean_object* v_x_314_){
_start:
{
lean_object* v___x_315_; lean_object* v_buckets_316_; lean_object* v___x_317_; lean_object* v___f_318_; lean_object* v___x_319_; size_t v_sz_320_; size_t v___x_321_; lean_object* v___x_322_; lean_object* v_fst_323_; 
v___x_315_ = ((lean_object*)(l_Std_HashMap_mapVals___redArg___closed__9));
v_buckets_316_ = lean_ctor_get(v_x_314_, 1);
lean_inc_ref(v_buckets_316_);
lean_dec_ref(v_x_314_);
v___x_317_ = lean_box(0);
v___f_318_ = ((lean_object*)(l_Std_HashMap_getAny_x3f___redArg___closed__1));
v___x_319_ = ((lean_object*)(l_Std_HashMap_getAny_x3f___redArg___closed__2));
v_sz_320_ = lean_array_size(v_buckets_316_);
v___x_321_ = ((size_t)0ULL);
v___x_322_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___redArg(v___x_315_, v_buckets_316_, v___f_318_, v_sz_320_, v___x_321_, v___x_319_);
v_fst_323_ = lean_ctor_get(v___x_322_, 0);
lean_inc(v_fst_323_);
lean_dec(v___x_322_);
if (lean_obj_tag(v_fst_323_) == 0)
{
return v___x_317_;
}
else
{
lean_object* v_val_324_; 
v_val_324_ = lean_ctor_get(v_fst_323_, 0);
lean_inc(v_val_324_);
lean_dec_ref_known(v_fst_323_, 1);
return v_val_324_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f(lean_object* v_00_u03b1_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_00_u03b2_328_, lean_object* v_x_329_){
_start:
{
lean_object* v___x_330_; 
v___x_330_ = l_Std_HashMap_getAny_x3f___redArg(v_x_329_);
return v___x_330_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___boxed(lean_object* v_00_u03b1_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_00_u03b2_334_, lean_object* v_x_335_){
_start:
{
lean_object* v_res_336_; 
v_res_336_ = l_Std_HashMap_getAny_x3f(v_00_u03b1_331_, v_inst_332_, v_inst_333_, v_00_u03b2_334_, v_x_335_);
lean_dec_ref(v_inst_333_);
lean_dec_ref(v_inst_332_);
return v_res_336_;
}
}
static lean_object* _init_l_instInhabitedEquation_default___closed__0(void){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_337_ = lean_box(0);
v___x_338_ = lean_unsigned_to_nat(16u);
v___x_339_ = lean_mk_array(v___x_338_, v___x_337_);
return v___x_339_;
}
}
static lean_object* _init_l_instInhabitedEquation_default___closed__1(void){
_start:
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_340_ = lean_obj_once(&l_instInhabitedEquation_default___closed__0, &l_instInhabitedEquation_default___closed__0_once, _init_l_instInhabitedEquation_default___closed__0);
v___x_341_ = lean_unsigned_to_nat(0u);
v___x_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_340_);
return v___x_342_;
}
}
static lean_object* _init_l_instInhabitedEquation_default___closed__2(void){
_start:
{
lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_343_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_344_ = lean_obj_once(&l_instInhabitedEquation_default___closed__1, &l_instInhabitedEquation_default___closed__1_once, _init_l_instInhabitedEquation_default___closed__1);
v___x_345_ = lean_unsigned_to_nat(0u);
v___x_346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v___x_344_);
lean_ctor_set(v___x_346_, 2, v___x_343_);
return v___x_346_;
}
}
static lean_object* _init_l_instInhabitedEquation_default(void){
_start:
{
lean_object* v___x_347_; 
v___x_347_ = lean_obj_once(&l_instInhabitedEquation_default___closed__2, &l_instInhabitedEquation_default___closed__2_once, _init_l_instInhabitedEquation_default___closed__2);
return v___x_347_;
}
}
static lean_object* _init_l_instInhabitedEquation(void){
_start:
{
lean_object* v___x_348_; 
v___x_348_ = l_instInhabitedEquation_default;
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__1(lean_object* v_x_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
return v_x_349_;
}
else
{
lean_object* v_value_351_; lean_object* v_tail_352_; lean_object* v___x_353_; 
v_value_351_ = lean_ctor_get(v_x_350_, 1);
v_tail_352_ = lean_ctor_get(v_x_350_, 2);
v___x_353_ = lean_nat_gcd(v_x_349_, v_value_351_);
lean_dec(v_x_349_);
v_x_349_ = v___x_353_;
v_x_350_ = v_tail_352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__1___boxed(lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__1(v_x_355_, v_x_356_);
lean_dec(v_x_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__2(lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_){
_start:
{
uint8_t v___x_362_; 
v___x_362_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_362_ == 0)
{
lean_object* v___x_363_; lean_object* v___x_364_; size_t v___x_365_; size_t v___x_366_; 
v___x_363_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
v___x_364_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__1(v_b_361_, v___x_363_);
v___x_365_ = ((size_t)1ULL);
v___x_366_ = lean_usize_add(v_i_359_, v___x_365_);
v_i_359_ = v___x_366_;
v_b_361_ = v___x_364_;
goto _start;
}
else
{
return v_b_361_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__2___boxed(lean_object* v_as_368_, lean_object* v_i_369_, lean_object* v_stop_370_, lean_object* v_b_371_){
_start:
{
size_t v_i_boxed_372_; size_t v_stop_boxed_373_; lean_object* v_res_374_; 
v_i_boxed_372_ = lean_unbox_usize(v_i_369_);
lean_dec(v_i_369_);
v_stop_boxed_373_ = lean_unbox_usize(v_stop_370_);
lean_dec(v_stop_370_);
v_res_374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__2(v_as_368_, v_i_boxed_372_, v_stop_boxed_373_, v_b_371_);
lean_dec_ref(v_as_368_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(lean_object* v_x_375_, lean_object* v_x_376_){
_start:
{
if (lean_obj_tag(v_x_376_) == 0)
{
return v_x_375_;
}
else
{
lean_object* v_key_377_; lean_object* v_value_378_; lean_object* v_tail_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_402_; 
v_key_377_ = lean_ctor_get(v_x_376_, 0);
v_value_378_ = lean_ctor_get(v_x_376_, 1);
v_tail_379_ = lean_ctor_get(v_x_376_, 2);
v_isSharedCheck_402_ = !lean_is_exclusive(v_x_376_);
if (v_isSharedCheck_402_ == 0)
{
v___x_381_ = v_x_376_;
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_tail_379_);
lean_inc(v_value_378_);
lean_inc(v_key_377_);
lean_dec(v_x_376_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_402_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; uint64_t v___x_384_; uint64_t v___x_385_; uint64_t v___x_386_; uint64_t v_fold_387_; uint64_t v___x_388_; uint64_t v___x_389_; uint64_t v___x_390_; size_t v___x_391_; size_t v___x_392_; size_t v___x_393_; size_t v___x_394_; size_t v___x_395_; lean_object* v___x_396_; lean_object* v___x_398_; 
v___x_383_ = lean_array_get_size(v_x_375_);
v___x_384_ = lean_uint64_of_nat(v_key_377_);
v___x_385_ = 32ULL;
v___x_386_ = lean_uint64_shift_right(v___x_384_, v___x_385_);
v_fold_387_ = lean_uint64_xor(v___x_384_, v___x_386_);
v___x_388_ = 16ULL;
v___x_389_ = lean_uint64_shift_right(v_fold_387_, v___x_388_);
v___x_390_ = lean_uint64_xor(v_fold_387_, v___x_389_);
v___x_391_ = lean_uint64_to_usize(v___x_390_);
v___x_392_ = lean_usize_of_nat(v___x_383_);
v___x_393_ = ((size_t)1ULL);
v___x_394_ = lean_usize_sub(v___x_392_, v___x_393_);
v___x_395_ = lean_usize_land(v___x_391_, v___x_394_);
v___x_396_ = lean_array_uget_borrowed(v_x_375_, v___x_395_);
lean_inc(v___x_396_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 2, v___x_396_);
v___x_398_ = v___x_381_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_key_377_);
lean_ctor_set(v_reuseFailAlloc_401_, 1, v_value_378_);
lean_ctor_set(v_reuseFailAlloc_401_, 2, v___x_396_);
v___x_398_ = v_reuseFailAlloc_401_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; 
v___x_399_ = lean_array_uset(v_x_375_, v___x_395_, v___x_398_);
v_x_375_ = v___x_399_;
v_x_376_ = v_tail_379_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_i_403_, lean_object* v_source_404_, lean_object* v_target_405_){
_start:
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = lean_array_get_size(v_source_404_);
v___x_407_ = lean_nat_dec_lt(v_i_403_, v___x_406_);
if (v___x_407_ == 0)
{
lean_dec_ref(v_source_404_);
lean_dec(v_i_403_);
return v_target_405_;
}
else
{
lean_object* v_es_408_; lean_object* v___x_409_; lean_object* v_source_410_; lean_object* v_target_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
v_es_408_ = lean_array_fget(v_source_404_, v_i_403_);
v___x_409_ = lean_box(0);
v_source_410_ = lean_array_fset(v_source_404_, v_i_403_, v___x_409_);
v_target_411_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_target_405_, v_es_408_);
v___x_412_ = lean_unsigned_to_nat(1u);
v___x_413_ = lean_nat_add(v_i_403_, v___x_412_);
lean_dec(v_i_403_);
v_i_403_ = v___x_413_;
v_source_404_ = v_source_410_;
v_target_405_ = v_target_411_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2___redArg(lean_object* v_data_415_){
_start:
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v_nbuckets_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_416_ = lean_array_get_size(v_data_415_);
v___x_417_ = lean_unsigned_to_nat(2u);
v_nbuckets_418_ = lean_nat_mul(v___x_416_, v___x_417_);
v___x_419_ = lean_unsigned_to_nat(0u);
v___x_420_ = lean_box(0);
v___x_421_ = lean_mk_array(v_nbuckets_418_, v___x_420_);
v___x_422_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7___redArg(v___x_419_, v_data_415_, v___x_421_);
return v___x_422_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg(lean_object* v_a_423_, lean_object* v_x_424_){
_start:
{
if (lean_obj_tag(v_x_424_) == 0)
{
uint8_t v___x_425_; 
v___x_425_ = 0;
return v___x_425_;
}
else
{
lean_object* v_key_426_; lean_object* v_tail_427_; uint8_t v___x_428_; 
v_key_426_ = lean_ctor_get(v_x_424_, 0);
v_tail_427_ = lean_ctor_get(v_x_424_, 2);
v___x_428_ = lean_nat_dec_eq(v_key_426_, v_a_423_);
if (v___x_428_ == 0)
{
v_x_424_ = v_tail_427_;
goto _start;
}
else
{
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_430_, lean_object* v_x_431_){
_start:
{
uint8_t v_res_432_; lean_object* v_r_433_; 
v_res_432_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg(v_a_430_, v_x_431_);
lean_dec(v_x_431_);
lean_dec(v_a_430_);
v_r_433_ = lean_box(v_res_432_);
return v_r_433_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__3___redArg(lean_object* v_a_434_, lean_object* v_b_435_, lean_object* v_x_436_){
_start:
{
if (lean_obj_tag(v_x_436_) == 0)
{
lean_dec(v_b_435_);
lean_dec(v_a_434_);
return v_x_436_;
}
else
{
lean_object* v_key_437_; lean_object* v_value_438_; lean_object* v_tail_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_451_; 
v_key_437_ = lean_ctor_get(v_x_436_, 0);
v_value_438_ = lean_ctor_get(v_x_436_, 1);
v_tail_439_ = lean_ctor_get(v_x_436_, 2);
v_isSharedCheck_451_ = !lean_is_exclusive(v_x_436_);
if (v_isSharedCheck_451_ == 0)
{
v___x_441_ = v_x_436_;
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_tail_439_);
lean_inc(v_value_438_);
lean_inc(v_key_437_);
lean_dec(v_x_436_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
uint8_t v___x_443_; 
v___x_443_ = lean_nat_dec_eq(v_key_437_, v_a_434_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; lean_object* v___x_446_; 
v___x_444_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__3___redArg(v_a_434_, v_b_435_, v_tail_439_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 2, v___x_444_);
v___x_446_ = v___x_441_;
goto v_reusejp_445_;
}
else
{
lean_object* v_reuseFailAlloc_447_; 
v_reuseFailAlloc_447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_447_, 0, v_key_437_);
lean_ctor_set(v_reuseFailAlloc_447_, 1, v_value_438_);
lean_ctor_set(v_reuseFailAlloc_447_, 2, v___x_444_);
v___x_446_ = v_reuseFailAlloc_447_;
goto v_reusejp_445_;
}
v_reusejp_445_:
{
return v___x_446_;
}
}
else
{
lean_object* v___x_449_; 
lean_dec(v_value_438_);
lean_dec(v_key_437_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v_b_435_);
lean_ctor_set(v___x_441_, 0, v_a_434_);
v___x_449_ = v___x_441_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_a_434_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_b_435_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_tail_439_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(lean_object* v_m_452_, lean_object* v_a_453_, lean_object* v_b_454_){
_start:
{
lean_object* v_size_455_; lean_object* v_buckets_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_499_; 
v_size_455_ = lean_ctor_get(v_m_452_, 0);
v_buckets_456_ = lean_ctor_get(v_m_452_, 1);
v_isSharedCheck_499_ = !lean_is_exclusive(v_m_452_);
if (v_isSharedCheck_499_ == 0)
{
v___x_458_ = v_m_452_;
v_isShared_459_ = v_isSharedCheck_499_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_buckets_456_);
lean_inc(v_size_455_);
lean_dec(v_m_452_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_499_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_460_; uint64_t v___x_461_; uint64_t v___x_462_; uint64_t v___x_463_; uint64_t v_fold_464_; uint64_t v___x_465_; uint64_t v___x_466_; uint64_t v___x_467_; size_t v___x_468_; size_t v___x_469_; size_t v___x_470_; size_t v___x_471_; size_t v___x_472_; lean_object* v_bkt_473_; uint8_t v___x_474_; 
v___x_460_ = lean_array_get_size(v_buckets_456_);
v___x_461_ = lean_uint64_of_nat(v_a_453_);
v___x_462_ = 32ULL;
v___x_463_ = lean_uint64_shift_right(v___x_461_, v___x_462_);
v_fold_464_ = lean_uint64_xor(v___x_461_, v___x_463_);
v___x_465_ = 16ULL;
v___x_466_ = lean_uint64_shift_right(v_fold_464_, v___x_465_);
v___x_467_ = lean_uint64_xor(v_fold_464_, v___x_466_);
v___x_468_ = lean_uint64_to_usize(v___x_467_);
v___x_469_ = lean_usize_of_nat(v___x_460_);
v___x_470_ = ((size_t)1ULL);
v___x_471_ = lean_usize_sub(v___x_469_, v___x_470_);
v___x_472_ = lean_usize_land(v___x_468_, v___x_471_);
v_bkt_473_ = lean_array_uget_borrowed(v_buckets_456_, v___x_472_);
v___x_474_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg(v_a_453_, v_bkt_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v_size_x27_476_; lean_object* v___x_477_; lean_object* v_buckets_x27_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_475_ = lean_unsigned_to_nat(1u);
v_size_x27_476_ = lean_nat_add(v_size_455_, v___x_475_);
lean_dec(v_size_455_);
lean_inc(v_bkt_473_);
v___x_477_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_477_, 0, v_a_453_);
lean_ctor_set(v___x_477_, 1, v_b_454_);
lean_ctor_set(v___x_477_, 2, v_bkt_473_);
v_buckets_x27_478_ = lean_array_uset(v_buckets_456_, v___x_472_, v___x_477_);
v___x_479_ = lean_unsigned_to_nat(4u);
v___x_480_ = lean_nat_mul(v_size_x27_476_, v___x_479_);
v___x_481_ = lean_unsigned_to_nat(3u);
v___x_482_ = lean_nat_div(v___x_480_, v___x_481_);
lean_dec(v___x_480_);
v___x_483_ = lean_array_get_size(v_buckets_x27_478_);
v___x_484_ = lean_nat_dec_le(v___x_482_, v___x_483_);
lean_dec(v___x_482_);
if (v___x_484_ == 0)
{
lean_object* v_val_485_; lean_object* v___x_487_; 
v_val_485_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2___redArg(v_buckets_x27_478_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v_val_485_);
lean_ctor_set(v___x_458_, 0, v_size_x27_476_);
v___x_487_ = v___x_458_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_size_x27_476_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_val_485_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
else
{
lean_object* v___x_490_; 
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v_buckets_x27_478_);
lean_ctor_set(v___x_458_, 0, v_size_x27_476_);
v___x_490_ = v___x_458_;
goto v_reusejp_489_;
}
else
{
lean_object* v_reuseFailAlloc_491_; 
v_reuseFailAlloc_491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_491_, 0, v_size_x27_476_);
lean_ctor_set(v_reuseFailAlloc_491_, 1, v_buckets_x27_478_);
v___x_490_ = v_reuseFailAlloc_491_;
goto v_reusejp_489_;
}
v_reusejp_489_:
{
return v___x_490_;
}
}
}
else
{
lean_object* v___x_492_; lean_object* v_buckets_x27_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_497_; 
lean_inc(v_bkt_473_);
v___x_492_ = lean_box(0);
v_buckets_x27_493_ = lean_array_uset(v_buckets_456_, v___x_472_, v___x_492_);
v___x_494_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__3___redArg(v_a_453_, v_b_454_, v_bkt_473_);
v___x_495_ = lean_array_uset(v_buckets_x27_493_, v___x_472_, v___x_494_);
if (v_isShared_459_ == 0)
{
lean_ctor_set(v___x_458_, 1, v___x_495_);
v___x_497_ = v___x_458_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_498_; 
v_reuseFailAlloc_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_498_, 0, v_size_455_);
lean_ctor_set(v_reuseFailAlloc_498_, 1, v___x_495_);
v___x_497_ = v_reuseFailAlloc_498_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
return v___x_497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__1___redArg(lean_object* v_f_500_, lean_object* v_x_501_, lean_object* v_x_502_){
_start:
{
if (lean_obj_tag(v_x_502_) == 0)
{
lean_dec(v_f_500_);
return v_x_501_;
}
else
{
lean_object* v_key_503_; lean_object* v_value_504_; lean_object* v_tail_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_key_503_ = lean_ctor_get(v_x_502_, 0);
lean_inc(v_key_503_);
v_value_504_ = lean_ctor_get(v_x_502_, 1);
lean_inc(v_value_504_);
v_tail_505_ = lean_ctor_get(v_x_502_, 2);
lean_inc(v_tail_505_);
lean_dec_ref_known(v_x_502_, 3);
lean_inc(v_f_500_);
v___x_506_ = lean_apply_1(v_f_500_, v_value_504_);
v___x_507_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_x_501_, v_key_503_, v___x_506_);
v_x_501_ = v___x_507_;
v_x_502_ = v_tail_505_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg(lean_object* v_f_509_, lean_object* v_as_510_, size_t v_i_511_, size_t v_stop_512_, lean_object* v_b_513_){
_start:
{
uint8_t v___x_514_; 
v___x_514_ = lean_usize_dec_eq(v_i_511_, v_stop_512_);
if (v___x_514_ == 0)
{
lean_object* v___x_515_; lean_object* v___x_516_; size_t v___x_517_; size_t v___x_518_; 
v___x_515_ = lean_array_uget_borrowed(v_as_510_, v_i_511_);
lean_inc(v___x_515_);
lean_inc(v_f_509_);
v___x_516_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__1___redArg(v_f_509_, v_b_513_, v___x_515_);
v___x_517_ = ((size_t)1ULL);
v___x_518_ = lean_usize_add(v_i_511_, v___x_517_);
v_i_511_ = v___x_518_;
v_b_513_ = v___x_516_;
goto _start;
}
else
{
lean_dec(v_f_509_);
return v_b_513_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg___boxed(lean_object* v_f_520_, lean_object* v_as_521_, lean_object* v_i_522_, lean_object* v_stop_523_, lean_object* v_b_524_){
_start:
{
size_t v_i_boxed_525_; size_t v_stop_boxed_526_; lean_object* v_res_527_; 
v_i_boxed_525_ = lean_unbox_usize(v_i_522_);
lean_dec(v_i_522_);
v_stop_boxed_526_ = lean_unbox_usize(v_stop_523_);
lean_dec(v_stop_523_);
v_res_527_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg(v_f_520_, v_as_521_, v_i_boxed_525_, v_stop_boxed_526_, v_b_524_);
lean_dec_ref(v_as_521_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___at___00gcd_spec__0___redArg(lean_object* v_f_528_, lean_object* v_xs_529_){
_start:
{
lean_object* v_size_530_; lean_object* v_buckets_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_555_; 
v_size_530_ = lean_ctor_get(v_xs_529_, 0);
v_buckets_531_ = lean_ctor_get(v_xs_529_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_xs_529_);
if (v_isSharedCheck_555_ == 0)
{
v___x_533_ = v_xs_529_;
v_isShared_534_ = v_isSharedCheck_555_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_buckets_531_);
lean_inc(v_size_530_);
lean_dec(v_xs_529_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_555_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_535_ = lean_unsigned_to_nat(0u);
v___x_536_ = lean_unsigned_to_nat(4u);
v___x_537_ = lean_nat_mul(v_size_530_, v___x_536_);
lean_dec(v_size_530_);
v___x_538_ = lean_unsigned_to_nat(3u);
v___x_539_ = lean_nat_div(v___x_537_, v___x_538_);
lean_dec(v___x_537_);
v___x_540_ = l_Nat_nextPowerOfTwo(v___x_539_);
lean_dec(v___x_539_);
v___x_541_ = lean_box(0);
v___x_542_ = lean_mk_array(v___x_540_, v___x_541_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 1, v___x_542_);
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_544_ = v___x_533_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v___x_535_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v___x_542_);
v___x_544_ = v_reuseFailAlloc_554_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_array_get_size(v_buckets_531_);
v___x_546_ = lean_nat_dec_lt(v___x_535_, v___x_545_);
if (v___x_546_ == 0)
{
lean_dec_ref(v_buckets_531_);
lean_dec(v_f_528_);
return v___x_544_;
}
else
{
uint8_t v___x_547_; 
v___x_547_ = lean_nat_dec_le(v___x_545_, v___x_545_);
if (v___x_547_ == 0)
{
if (v___x_546_ == 0)
{
lean_dec_ref(v_buckets_531_);
lean_dec(v_f_528_);
return v___x_544_;
}
else
{
size_t v___x_548_; size_t v___x_549_; lean_object* v___x_550_; 
v___x_548_ = ((size_t)0ULL);
v___x_549_ = lean_usize_of_nat(v___x_545_);
v___x_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg(v_f_528_, v_buckets_531_, v___x_548_, v___x_549_, v___x_544_);
lean_dec_ref(v_buckets_531_);
return v___x_550_;
}
}
else
{
size_t v___x_551_; size_t v___x_552_; lean_object* v___x_553_; 
v___x_551_ = ((size_t)0ULL);
v___x_552_ = lean_usize_of_nat(v___x_545_);
v___x_553_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg(v_f_528_, v_buckets_531_, v___x_551_, v___x_552_, v___x_544_);
lean_dec_ref(v_buckets_531_);
return v___x_553_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__3(lean_object* v_x_556_, lean_object* v_x_557_){
_start:
{
if (lean_obj_tag(v_x_557_) == 0)
{
return v_x_556_;
}
else
{
lean_object* v_key_558_; lean_object* v_value_559_; lean_object* v_tail_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
v_key_558_ = lean_ctor_get(v_x_557_, 0);
v_value_559_ = lean_ctor_get(v_x_557_, 1);
v_tail_560_ = lean_ctor_get(v_x_557_, 2);
lean_inc(v_value_559_);
lean_inc(v_key_558_);
v___x_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_561_, 0, v_key_558_);
lean_ctor_set(v___x_561_, 1, v_value_559_);
v___x_562_ = lean_array_push(v_x_556_, v___x_561_);
v_x_556_ = v___x_562_;
v_x_557_ = v_tail_560_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__3___boxed(lean_object* v_x_564_, lean_object* v_x_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__3(v_x_564_, v_x_565_);
lean_dec(v_x_565_);
return v_res_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__4(lean_object* v_as_567_, size_t v_i_568_, size_t v_stop_569_, lean_object* v_b_570_){
_start:
{
uint8_t v___x_571_; 
v___x_571_ = lean_usize_dec_eq(v_i_568_, v_stop_569_);
if (v___x_571_ == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; 
v___x_572_ = lean_array_uget_borrowed(v_as_567_, v_i_568_);
v___x_573_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00gcd_spec__3(v_b_570_, v___x_572_);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_add(v_i_568_, v___x_574_);
v_i_568_ = v___x_575_;
v_b_570_ = v___x_573_;
goto _start;
}
else
{
return v_b_570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__4___boxed(lean_object* v_as_577_, lean_object* v_i_578_, lean_object* v_stop_579_, lean_object* v_b_580_){
_start:
{
size_t v_i_boxed_581_; size_t v_stop_boxed_582_; lean_object* v_res_583_; 
v_i_boxed_581_ = lean_unbox_usize(v_i_578_);
lean_dec(v_i_578_);
v_stop_boxed_582_ = lean_unbox_usize(v_stop_579_);
lean_dec(v_stop_579_);
v_res_583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__4(v_as_577_, v_i_boxed_581_, v_stop_boxed_582_, v_b_580_);
lean_dec_ref(v_as_577_);
return v_res_583_;
}
}
static lean_object* _init_l_gcd___closed__5(void){
_start:
{
lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_590_ = ((lean_object*)(l_gcd___closed__4));
v___x_591_ = lean_unsigned_to_nat(21u);
v___x_592_ = lean_unsigned_to_nat(88u);
v___x_593_ = ((lean_object*)(l_gcd___closed__3));
v___x_594_ = ((lean_object*)(l_gcd___closed__2));
v___x_595_ = l_mkPanicMessageWithDecl(v___x_594_, v___x_593_, v___x_592_, v___x_591_, v___x_590_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_gcd(lean_object* v_coeffs_596_){
_start:
{
lean_object* v___f_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v_coeffs_600_; lean_object* v___y_602_; lean_object* v_size_626_; lean_object* v_buckets_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v___f_597_ = ((lean_object*)(l_gcd___closed__0));
v___x_598_ = lean_unsigned_to_nat(0u);
v___x_599_ = ((lean_object*)(l_gcd___closed__1));
v_coeffs_600_ = l_Std_HashMap_mapVals___at___00gcd_spec__0___redArg(v___f_597_, v_coeffs_596_);
v_size_626_ = lean_ctor_get(v_coeffs_600_, 0);
lean_inc(v_size_626_);
v_buckets_627_ = lean_ctor_get(v_coeffs_600_, 1);
lean_inc_ref(v_buckets_627_);
v___x_628_ = lean_mk_empty_array_with_capacity(v_size_626_);
lean_dec(v_size_626_);
v___x_629_ = lean_array_get_size(v_buckets_627_);
v___x_630_ = lean_nat_dec_lt(v___x_598_, v___x_629_);
if (v___x_630_ == 0)
{
lean_dec_ref(v_buckets_627_);
v___y_602_ = v___x_628_;
goto v___jp_601_;
}
else
{
uint8_t v___x_631_; 
v___x_631_ = lean_nat_dec_le(v___x_629_, v___x_629_);
if (v___x_631_ == 0)
{
if (v___x_630_ == 0)
{
lean_dec_ref(v_buckets_627_);
v___y_602_ = v___x_628_;
goto v___jp_601_;
}
else
{
size_t v___x_632_; size_t v___x_633_; lean_object* v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_629_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__4(v_buckets_627_, v___x_632_, v___x_633_, v___x_628_);
lean_dec_ref(v_buckets_627_);
v___y_602_ = v___x_634_;
goto v___jp_601_;
}
}
else
{
size_t v___x_635_; size_t v___x_636_; lean_object* v___x_637_; 
v___x_635_ = ((size_t)0ULL);
v___x_636_ = lean_usize_of_nat(v___x_629_);
v___x_637_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__4(v_buckets_627_, v___x_635_, v___x_636_, v___x_628_);
lean_dec_ref(v_buckets_627_);
v___y_602_ = v___x_637_;
goto v___jp_601_;
}
}
v___jp_601_:
{
lean_object* v___x_603_; uint8_t v___x_604_; 
v___x_603_ = lean_array_get_size(v___y_602_);
v___x_604_ = lean_nat_dec_eq(v___x_603_, v___x_598_);
if (v___x_604_ == 0)
{
lean_object* v___x_605_; uint8_t v___x_606_; 
v___x_605_ = lean_unsigned_to_nat(1u);
v___x_606_ = lean_nat_dec_eq(v___x_603_, v___x_605_);
if (v___x_606_ == 0)
{
lean_object* v___x_607_; lean_object* v_snd_608_; lean_object* v___x_609_; lean_object* v_snd_610_; lean_object* v_buckets_611_; lean_object* v___x_612_; lean_object* v___x_613_; uint8_t v___x_614_; 
v___x_607_ = lean_array_get_borrowed(v___x_599_, v___y_602_, v___x_598_);
v_snd_608_ = lean_ctor_get(v___x_607_, 1);
lean_inc(v_snd_608_);
v___x_609_ = lean_array_get(v___x_599_, v___y_602_, v___x_605_);
lean_dec_ref(v___y_602_);
v_snd_610_ = lean_ctor_get(v___x_609_, 1);
lean_inc(v_snd_610_);
lean_dec(v___x_609_);
v_buckets_611_ = lean_ctor_get(v_coeffs_600_, 1);
lean_inc_ref(v_buckets_611_);
lean_dec_ref(v_coeffs_600_);
v___x_612_ = lean_nat_gcd(v_snd_608_, v_snd_610_);
lean_dec(v_snd_610_);
lean_dec(v_snd_608_);
v___x_613_ = lean_array_get_size(v_buckets_611_);
v___x_614_ = lean_nat_dec_lt(v___x_598_, v___x_613_);
if (v___x_614_ == 0)
{
lean_dec_ref(v_buckets_611_);
return v___x_612_;
}
else
{
uint8_t v___x_615_; 
v___x_615_ = lean_nat_dec_le(v___x_613_, v___x_613_);
if (v___x_615_ == 0)
{
if (v___x_614_ == 0)
{
lean_dec_ref(v_buckets_611_);
return v___x_612_;
}
else
{
size_t v___x_616_; size_t v___x_617_; lean_object* v___x_618_; 
v___x_616_ = ((size_t)0ULL);
v___x_617_ = lean_usize_of_nat(v___x_613_);
v___x_618_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__2(v_buckets_611_, v___x_616_, v___x_617_, v___x_612_);
lean_dec_ref(v_buckets_611_);
return v___x_618_;
}
}
else
{
size_t v___x_619_; size_t v___x_620_; lean_object* v___x_621_; 
v___x_619_ = ((size_t)0ULL);
v___x_620_ = lean_usize_of_nat(v___x_613_);
v___x_621_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00gcd_spec__2(v_buckets_611_, v___x_619_, v___x_620_, v___x_612_);
lean_dec_ref(v_buckets_611_);
return v___x_621_;
}
}
}
else
{
lean_object* v___x_622_; lean_object* v_snd_623_; 
lean_dec_ref(v_coeffs_600_);
v___x_622_ = lean_array_fget(v___y_602_, v___x_598_);
lean_dec_ref(v___y_602_);
v_snd_623_ = lean_ctor_get(v___x_622_, 1);
lean_inc(v_snd_623_);
lean_dec(v___x_622_);
return v_snd_623_;
}
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
lean_dec_ref(v___y_602_);
lean_dec_ref(v_coeffs_600_);
v___x_624_ = lean_obj_once(&l_gcd___closed__5, &l_gcd___closed__5_once, _init_l_gcd___closed__5);
v___x_625_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_624_);
return v___x_625_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapVals___at___00gcd_spec__0(lean_object* v_00_u03b2_638_, lean_object* v_00_u03b3_639_, lean_object* v_f_640_, lean_object* v_xs_641_){
_start:
{
lean_object* v___x_642_; 
v___x_642_ = l_Std_HashMap_mapVals___at___00gcd_spec__0___redArg(v_f_640_, v_xs_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0(lean_object* v_00_u03b2_643_, lean_object* v_m_644_, lean_object* v_a_645_, lean_object* v_b_646_){
_start:
{
lean_object* v___x_647_; 
v___x_647_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_m_644_, v_a_645_, v_b_646_);
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__1(lean_object* v_00_u03b2_648_, lean_object* v_00_u03b3_649_, lean_object* v_f_650_, lean_object* v_x_651_, lean_object* v_x_652_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__1___redArg(v_f_650_, v_x_651_, v_x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2(lean_object* v_00_u03b2_654_, lean_object* v_00_u03b3_655_, lean_object* v_f_656_, lean_object* v_as_657_, size_t v_i_658_, size_t v_stop_659_, lean_object* v_b_660_){
_start:
{
lean_object* v___x_661_; 
v___x_661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___redArg(v_f_656_, v_as_657_, v_i_658_, v_stop_659_, v_b_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2___boxed(lean_object* v_00_u03b2_662_, lean_object* v_00_u03b3_663_, lean_object* v_f_664_, lean_object* v_as_665_, lean_object* v_i_666_, lean_object* v_stop_667_, lean_object* v_b_668_){
_start:
{
size_t v_i_boxed_669_; size_t v_stop_boxed_670_; lean_object* v_res_671_; 
v_i_boxed_669_ = lean_unbox_usize(v_i_666_);
lean_dec(v_i_666_);
v_stop_boxed_670_ = lean_unbox_usize(v_stop_667_);
lean_dec(v_stop_667_);
v_res_671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__2(v_00_u03b2_662_, v_00_u03b3_663_, v_f_664_, v_as_665_, v_i_boxed_669_, v_stop_boxed_670_, v_b_668_);
lean_dec_ref(v_as_665_);
return v_res_671_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_672_, lean_object* v_a_673_, lean_object* v_x_674_){
_start:
{
uint8_t v___x_675_; 
v___x_675_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg(v_a_673_, v_x_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_676_, lean_object* v_a_677_, lean_object* v_x_678_){
_start:
{
uint8_t v_res_679_; lean_object* v_r_680_; 
v_res_679_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1(v_00_u03b2_676_, v_a_677_, v_x_678_);
lean_dec(v_x_678_);
lean_dec(v_a_677_);
v_r_680_ = lean_box(v_res_679_);
return v_r_680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_681_, lean_object* v_data_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2___redArg(v_data_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_684_, lean_object* v_a_685_, lean_object* v_b_686_, lean_object* v_x_687_){
_start:
{
lean_object* v___x_688_; 
v___x_688_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__3___redArg(v_a_685_, v_b_686_, v_x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7(lean_object* v_00_u03b2_689_, lean_object* v_i_690_, lean_object* v_source_691_, lean_object* v_target_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7___redArg(v_i_690_, v_source_691_, v_target_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7_spec__10(lean_object* v_00_u03b2_694_, lean_object* v_x_695_, lean_object* v_x_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__2_spec__7_spec__10___redArg(v_x_695_, v_x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Equation_preprocess_x3f___lam__0(lean_object* v_gcd_698_, lean_object* v_x_699_, lean_object* v_coeff_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = lean_int_ediv(v_coeff_700_, v_gcd_698_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Equation_preprocess_x3f___lam__0___boxed(lean_object* v_gcd_702_, lean_object* v_x_703_, lean_object* v_coeff_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_Equation_preprocess_x3f___lam__0(v_gcd_702_, v_x_703_, v_coeff_704_);
lean_dec(v_coeff_704_);
lean_dec(v_x_703_);
lean_dec(v_gcd_702_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_f_706_, lean_object* v_acc_707_, lean_object* v_a_708_){
_start:
{
if (lean_obj_tag(v_a_708_) == 0)
{
lean_dec(v_f_706_);
return v_acc_707_;
}
else
{
lean_object* v_key_709_; lean_object* v_value_710_; lean_object* v_tail_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_720_; 
v_key_709_ = lean_ctor_get(v_a_708_, 0);
v_value_710_ = lean_ctor_get(v_a_708_, 1);
v_tail_711_ = lean_ctor_get(v_a_708_, 2);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_720_ == 0)
{
v___x_713_ = v_a_708_;
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_tail_711_);
lean_inc(v_value_710_);
lean_inc(v_key_709_);
lean_dec(v_a_708_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_720_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_715_; lean_object* v___x_717_; 
lean_inc(v_f_706_);
lean_inc(v_key_709_);
v___x_715_ = lean_apply_2(v_f_706_, v_key_709_, v_value_710_);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 2, v_acc_707_);
lean_ctor_set(v___x_713_, 1, v___x_715_);
v___x_717_ = v___x_713_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_key_709_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_719_, 2, v_acc_707_);
v___x_717_ = v_reuseFailAlloc_719_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v_acc_707_ = v___x_717_;
v_a_708_ = v_tail_711_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___redArg(lean_object* v_f_721_, size_t v_sz_722_, size_t v_i_723_, lean_object* v_bs_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = lean_usize_dec_lt(v_i_723_, v_sz_722_);
if (v___x_725_ == 0)
{
lean_dec(v_f_721_);
return v_bs_724_;
}
else
{
lean_object* v_v_726_; lean_object* v___x_727_; lean_object* v_bs_x27_728_; lean_object* v___x_729_; lean_object* v___x_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; 
v_v_726_ = lean_array_uget(v_bs_724_, v_i_723_);
v___x_727_ = lean_unsigned_to_nat(0u);
v_bs_x27_728_ = lean_array_uset(v_bs_724_, v_i_723_, v___x_727_);
v___x_729_ = lean_box(0);
lean_inc(v_f_721_);
v___x_730_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__1___redArg(v_f_721_, v___x_729_, v_v_726_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_i_723_, v___x_731_);
v___x_733_ = lean_array_uset(v_bs_x27_728_, v_i_723_, v___x_730_);
v_i_723_ = v___x_732_;
v_bs_724_ = v___x_733_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_f_735_, lean_object* v_sz_736_, lean_object* v_i_737_, lean_object* v_bs_738_){
_start:
{
size_t v_sz_boxed_739_; size_t v_i_boxed_740_; lean_object* v_res_741_; 
v_sz_boxed_739_ = lean_unbox_usize(v_sz_736_);
lean_dec(v_sz_736_);
v_i_boxed_740_ = lean_unbox_usize(v_i_737_);
lean_dec(v_i_737_);
v_res_741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___redArg(v_f_735_, v_sz_boxed_739_, v_i_boxed_740_, v_bs_738_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(lean_object* v_f_742_, lean_object* v_m_743_){
_start:
{
lean_object* v_size_744_; lean_object* v_buckets_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_755_; 
v_size_744_ = lean_ctor_get(v_m_743_, 0);
v_buckets_745_ = lean_ctor_get(v_m_743_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_m_743_);
if (v_isSharedCheck_755_ == 0)
{
v___x_747_ = v_m_743_;
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_buckets_745_);
lean_inc(v_size_744_);
lean_dec(v_m_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_755_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
size_t v_sz_749_; size_t v___x_750_; lean_object* v_newBuckets_751_; lean_object* v___x_753_; 
v_sz_749_ = lean_array_size(v_buckets_745_);
v___x_750_ = ((size_t)0ULL);
v_newBuckets_751_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___redArg(v_f_742_, v_sz_749_, v___x_750_, v_buckets_745_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_newBuckets_751_);
v___x_753_ = v___x_747_;
goto v_reusejp_752_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_size_744_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_newBuckets_751_);
v___x_753_ = v_reuseFailAlloc_754_;
goto v_reusejp_752_;
}
v_reusejp_752_:
{
return v___x_753_;
}
}
}
}
LEAN_EXPORT lean_object* l_Equation_preprocess_x3f(lean_object* v_e_756_){
_start:
{
lean_object* v_id_757_; lean_object* v_coeffs_758_; lean_object* v_const_759_; lean_object* v___x_761_; uint8_t v_isShared_762_; uint8_t v_isSharedCheck_776_; 
v_id_757_ = lean_ctor_get(v_e_756_, 0);
v_coeffs_758_ = lean_ctor_get(v_e_756_, 1);
v_const_759_ = lean_ctor_get(v_e_756_, 2);
v_isSharedCheck_776_ = !lean_is_exclusive(v_e_756_);
if (v_isSharedCheck_776_ == 0)
{
v___x_761_ = v_e_756_;
v_isShared_762_ = v_isSharedCheck_776_;
goto v_resetjp_760_;
}
else
{
lean_inc(v_const_759_);
lean_inc(v_coeffs_758_);
lean_inc(v_id_757_);
lean_dec(v_e_756_);
v___x_761_ = lean_box(0);
v_isShared_762_ = v_isSharedCheck_776_;
goto v_resetjp_760_;
}
v_resetjp_760_:
{
lean_object* v___x_763_; lean_object* v_gcd_764_; lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
lean_inc_ref(v_coeffs_758_);
v___x_763_ = l_gcd(v_coeffs_758_);
v_gcd_764_ = lean_nat_to_int(v___x_763_);
v___x_765_ = lean_int_emod(v_const_759_, v_gcd_764_);
v___x_766_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_767_ = lean_int_dec_eq(v___x_765_, v___x_766_);
lean_dec(v___x_765_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec(v_gcd_764_);
lean_del_object(v___x_761_);
lean_dec(v_const_759_);
lean_dec_ref(v_coeffs_758_);
lean_dec(v_id_757_);
v___x_768_ = lean_box(0);
return v___x_768_;
}
else
{
lean_object* v___f_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_773_; 
lean_inc(v_gcd_764_);
v___f_769_ = lean_alloc_closure((void*)(l_Equation_preprocess_x3f___lam__0___boxed), 3, 1);
lean_closure_set(v___f_769_, 0, v_gcd_764_);
v___x_770_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v___f_769_, v_coeffs_758_);
v___x_771_ = lean_int_ediv(v_const_759_, v_gcd_764_);
lean_dec(v_gcd_764_);
lean_dec(v_const_759_);
if (v_isShared_762_ == 0)
{
lean_ctor_set(v___x_761_, 2, v___x_771_);
lean_ctor_set(v___x_761_, 1, v___x_770_);
v___x_773_ = v___x_761_;
goto v_reusejp_772_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_id_757_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v___x_770_);
lean_ctor_set(v_reuseFailAlloc_775_, 2, v___x_771_);
v___x_773_ = v_reuseFailAlloc_775_;
goto v_reusejp_772_;
}
v_reusejp_772_:
{
lean_object* v___x_774_; 
v___x_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_774_, 0, v___x_773_);
return v___x_774_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0___redArg(lean_object* v_f_777_, lean_object* v_xs_778_){
_start:
{
lean_object* v___x_779_; 
v___x_779_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v_f_777_, v_xs_778_);
return v___x_779_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0(lean_object* v_00_u03b2_780_, lean_object* v_f_781_, lean_object* v_xs_782_){
_start:
{
lean_object* v___x_783_; 
v___x_783_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v_f_781_, v_xs_782_);
return v___x_783_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0(lean_object* v_00_u03b2_784_, lean_object* v_f_785_, lean_object* v_m_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v_f_785_, v_m_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_788_, lean_object* v_f_789_, lean_object* v_acc_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_map_go___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__1___redArg(v_f_789_, v_acc_790_, v_a_791_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_793_, lean_object* v_f_794_, size_t v_sz_795_, size_t v_i_796_, lean_object* v_bs_797_){
_start:
{
lean_object* v___x_798_; 
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___redArg(v_f_794_, v_sz_795_, v_i_796_, v_bs_797_);
return v___x_798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_799_, lean_object* v_f_800_, lean_object* v_sz_801_, lean_object* v_i_802_, lean_object* v_bs_803_){
_start:
{
size_t v_sz_boxed_804_; size_t v_i_boxed_805_; lean_object* v_res_806_; 
v_sz_boxed_804_ = lean_unbox_usize(v_sz_801_);
lean_dec(v_sz_801_);
v_i_boxed_805_ = lean_unbox_usize(v_i_802_);
lean_dec(v_i_802_);
v_res_806_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0_spec__2(v_00_u03b2_799_, v_f_800_, v_sz_boxed_804_, v_i_boxed_805_, v_bs_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___redArg(lean_object* v_a_807_, lean_object* v_x_808_){
_start:
{
if (lean_obj_tag(v_x_808_) == 0)
{
lean_object* v___x_809_; 
v___x_809_ = lean_box(0);
return v___x_809_;
}
else
{
lean_object* v_key_810_; lean_object* v_value_811_; lean_object* v_tail_812_; uint8_t v___x_813_; 
v_key_810_ = lean_ctor_get(v_x_808_, 0);
v_value_811_ = lean_ctor_get(v_x_808_, 1);
v_tail_812_ = lean_ctor_get(v_x_808_, 2);
v___x_813_ = lean_nat_dec_eq(v_key_810_, v_a_807_);
if (v___x_813_ == 0)
{
v_x_808_ = v_tail_812_;
goto _start;
}
else
{
lean_object* v___x_815_; 
lean_inc(v_value_811_);
v___x_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_815_, 0, v_value_811_);
return v___x_815_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___redArg___boxed(lean_object* v_a_816_, lean_object* v_x_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___redArg(v_a_816_, v_x_817_);
lean_dec(v_x_817_);
lean_dec(v_a_816_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg(lean_object* v_m_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_buckets_821_; lean_object* v___x_822_; uint64_t v___x_823_; uint64_t v___x_824_; uint64_t v___x_825_; uint64_t v_fold_826_; uint64_t v___x_827_; uint64_t v___x_828_; uint64_t v___x_829_; size_t v___x_830_; size_t v___x_831_; size_t v___x_832_; size_t v___x_833_; size_t v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; 
v_buckets_821_ = lean_ctor_get(v_m_819_, 1);
v___x_822_ = lean_array_get_size(v_buckets_821_);
v___x_823_ = lean_uint64_of_nat(v_a_820_);
v___x_824_ = 32ULL;
v___x_825_ = lean_uint64_shift_right(v___x_823_, v___x_824_);
v_fold_826_ = lean_uint64_xor(v___x_823_, v___x_825_);
v___x_827_ = 16ULL;
v___x_828_ = lean_uint64_shift_right(v_fold_826_, v___x_827_);
v___x_829_ = lean_uint64_xor(v_fold_826_, v___x_828_);
v___x_830_ = lean_uint64_to_usize(v___x_829_);
v___x_831_ = lean_usize_of_nat(v___x_822_);
v___x_832_ = ((size_t)1ULL);
v___x_833_ = lean_usize_sub(v___x_831_, v___x_832_);
v___x_834_ = lean_usize_land(v___x_830_, v___x_833_);
v___x_835_ = lean_array_uget_borrowed(v_buckets_821_, v___x_834_);
v___x_836_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___redArg(v_a_820_, v___x_835_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg___boxed(lean_object* v_m_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg(v_m_837_, v_a_838_);
lean_dec(v_a_838_);
lean_dec_ref(v_m_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Equation_subst___lam__0(lean_object* v_coeffs_840_, lean_object* v_s_u2096_841_, lean_object* v_b_u2096_842_, lean_object* v_i_843_, lean_object* v_b_u1d62_844_){
_start:
{
lean_object* v___x_845_; 
v___x_845_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg(v_coeffs_840_, v_i_843_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_inc(v_b_u1d62_844_);
return v_b_u1d62_844_;
}
else
{
lean_object* v_val_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v_val_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_val_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = lean_int_mul(v_s_u2096_841_, v_b_u2096_842_);
v___x_848_ = lean_int_mul(v___x_847_, v_val_846_);
lean_dec(v_val_846_);
lean_dec(v___x_847_);
v___x_849_ = lean_int_sub(v_b_u1d62_844_, v___x_848_);
lean_dec(v___x_848_);
return v___x_849_;
}
}
}
LEAN_EXPORT lean_object* l_Equation_subst___lam__0___boxed(lean_object* v_coeffs_850_, lean_object* v_s_u2096_851_, lean_object* v_b_u2096_852_, lean_object* v_i_853_, lean_object* v_b_u1d62_854_){
_start:
{
lean_object* v_res_855_; 
v_res_855_ = l_Equation_subst___lam__0(v_coeffs_850_, v_s_u2096_851_, v_b_u2096_852_, v_i_853_, v_b_u1d62_854_);
lean_dec(v_b_u1d62_854_);
lean_dec(v_i_853_);
lean_dec(v_b_u2096_852_);
lean_dec(v_s_u2096_851_);
lean_dec_ref(v_coeffs_850_);
return v_res_855_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg(lean_object* v_m_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_buckets_858_; lean_object* v___x_859_; uint64_t v___x_860_; uint64_t v___x_861_; uint64_t v___x_862_; uint64_t v_fold_863_; uint64_t v___x_864_; uint64_t v___x_865_; uint64_t v___x_866_; size_t v___x_867_; size_t v___x_868_; size_t v___x_869_; size_t v___x_870_; size_t v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_buckets_858_ = lean_ctor_get(v_m_856_, 1);
v___x_859_ = lean_array_get_size(v_buckets_858_);
v___x_860_ = lean_uint64_of_nat(v_a_857_);
v___x_861_ = 32ULL;
v___x_862_ = lean_uint64_shift_right(v___x_860_, v___x_861_);
v_fold_863_ = lean_uint64_xor(v___x_860_, v___x_862_);
v___x_864_ = 16ULL;
v___x_865_ = lean_uint64_shift_right(v_fold_863_, v___x_864_);
v___x_866_ = lean_uint64_xor(v_fold_863_, v___x_865_);
v___x_867_ = lean_uint64_to_usize(v___x_866_);
v___x_868_ = lean_usize_of_nat(v___x_859_);
v___x_869_ = ((size_t)1ULL);
v___x_870_ = lean_usize_sub(v___x_868_, v___x_869_);
v___x_871_ = lean_usize_land(v___x_867_, v___x_870_);
v___x_872_ = lean_array_uget_borrowed(v_buckets_858_, v___x_871_);
v___x_873_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg(v_a_857_, v___x_872_);
return v___x_873_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg___boxed(lean_object* v_m_874_, lean_object* v_a_875_){
_start:
{
uint8_t v_res_876_; lean_object* v_r_877_; 
v_res_876_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg(v_m_874_, v_a_875_);
lean_dec(v_a_875_);
lean_dec_ref(v_m_874_);
v_r_877_ = lean_box(v_res_876_);
return v_r_877_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_subst_spec__2(lean_object* v_s_u2096_878_, lean_object* v_b_u2096_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
if (lean_obj_tag(v_a_880_) == 0)
{
lean_object* v___x_882_; 
v___x_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_882_, 0, v_a_881_);
return v___x_882_;
}
else
{
lean_object* v_key_883_; lean_object* v_value_884_; lean_object* v_tail_885_; uint8_t v___x_886_; 
v_key_883_ = lean_ctor_get(v_a_880_, 0);
lean_inc(v_key_883_);
v_value_884_ = lean_ctor_get(v_a_880_, 1);
lean_inc(v_value_884_);
v_tail_885_ = lean_ctor_get(v_a_880_, 2);
lean_inc(v_tail_885_);
lean_dec_ref_known(v_a_880_, 3);
v___x_886_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg(v_a_881_, v_key_883_);
if (v___x_886_ == 0)
{
lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; 
v___x_887_ = lean_int_neg(v_s_u2096_878_);
v___x_888_ = lean_int_mul(v___x_887_, v_b_u2096_879_);
lean_dec(v___x_887_);
v___x_889_ = lean_int_mul(v___x_888_, v_value_884_);
lean_dec(v_value_884_);
lean_dec(v___x_888_);
v___x_890_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_a_881_, v_key_883_, v___x_889_);
v_a_880_ = v_tail_885_;
v_a_881_ = v___x_890_;
goto _start;
}
else
{
lean_dec(v_value_884_);
lean_dec(v_key_883_);
v_a_880_ = v_tail_885_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_subst_spec__2___boxed(lean_object* v_s_u2096_893_, lean_object* v_b_u2096_894_, lean_object* v_a_895_, lean_object* v_a_896_){
_start:
{
lean_object* v_res_897_; 
v_res_897_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_subst_spec__2(v_s_u2096_893_, v_b_u2096_894_, v_a_895_, v_a_896_);
lean_dec(v_b_u2096_894_);
lean_dec(v_s_u2096_893_);
return v_res_897_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_subst_spec__4(lean_object* v_s_u2096_898_, lean_object* v_b_u2096_899_, lean_object* v_as_900_, size_t v_sz_901_, size_t v_i_902_, lean_object* v_b_903_){
_start:
{
uint8_t v___x_904_; 
v___x_904_ = lean_usize_dec_lt(v_i_902_, v_sz_901_);
if (v___x_904_ == 0)
{
return v_b_903_;
}
else
{
lean_object* v_a_905_; lean_object* v___x_906_; 
v_a_905_ = lean_array_uget_borrowed(v_as_900_, v_i_902_);
lean_inc(v_a_905_);
v___x_906_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_subst_spec__2(v_s_u2096_898_, v_b_u2096_899_, v_a_905_, v_b_903_);
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v_a_907_; 
v_a_907_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_907_);
lean_dec_ref_known(v___x_906_, 1);
return v_a_907_;
}
else
{
lean_object* v_a_908_; size_t v___x_909_; size_t v___x_910_; 
v_a_908_ = lean_ctor_get(v___x_906_, 0);
lean_inc(v_a_908_);
lean_dec_ref_known(v___x_906_, 1);
v___x_909_ = ((size_t)1ULL);
v___x_910_ = lean_usize_add(v_i_902_, v___x_909_);
v_i_902_ = v___x_910_;
v_b_903_ = v_a_908_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_subst_spec__4___boxed(lean_object* v_s_u2096_912_, lean_object* v_b_u2096_913_, lean_object* v_as_914_, lean_object* v_sz_915_, lean_object* v_i_916_, lean_object* v_b_917_){
_start:
{
size_t v_sz_boxed_918_; size_t v_i_boxed_919_; lean_object* v_res_920_; 
v_sz_boxed_918_ = lean_unbox_usize(v_sz_915_);
lean_dec(v_sz_915_);
v_i_boxed_919_ = lean_unbox_usize(v_i_916_);
lean_dec(v_i_916_);
v_res_920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_subst_spec__4(v_s_u2096_912_, v_b_u2096_913_, v_as_914_, v_sz_boxed_918_, v_i_boxed_919_, v_b_917_);
lean_dec_ref(v_as_914_);
lean_dec(v_b_u2096_913_);
lean_dec(v_s_u2096_912_);
return v_res_920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(lean_object* v_as_921_, size_t v_i_922_, size_t v_stop_923_, lean_object* v_b_924_){
_start:
{
uint8_t v___x_925_; 
v___x_925_ = lean_usize_dec_eq(v_i_922_, v_stop_923_);
if (v___x_925_ == 0)
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; size_t v___x_929_; size_t v___x_930_; 
v___x_926_ = lean_array_uget_borrowed(v_as_921_, v_i_922_);
v___x_927_ = l_Std_DHashMap_Internal_AssocList_length___redArg(v___x_926_);
v___x_928_ = lean_nat_add(v_b_924_, v___x_927_);
lean_dec(v___x_927_);
lean_dec(v_b_924_);
v___x_929_ = ((size_t)1ULL);
v___x_930_ = lean_usize_add(v_i_922_, v___x_929_);
v_i_922_ = v___x_930_;
v_b_924_ = v___x_928_;
goto _start;
}
else
{
return v_b_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9___boxed(lean_object* v_as_932_, lean_object* v_i_933_, lean_object* v_stop_934_, lean_object* v_b_935_){
_start:
{
size_t v_i_boxed_936_; size_t v_stop_boxed_937_; lean_object* v_res_938_; 
v_i_boxed_936_ = lean_unbox_usize(v_i_933_);
lean_dec(v_i_933_);
v_stop_boxed_937_ = lean_unbox_usize(v_stop_934_);
lean_dec(v_stop_934_);
v_res_938_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(v_as_932_, v_i_boxed_936_, v_stop_boxed_937_, v_b_935_);
lean_dec_ref(v_as_932_);
return v_res_938_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__7(lean_object* v_varIdx_939_, lean_object* v_acc_940_, lean_object* v_a_941_){
_start:
{
if (lean_obj_tag(v_a_941_) == 0)
{
return v_acc_940_;
}
else
{
lean_object* v_key_942_; lean_object* v_value_943_; lean_object* v_tail_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_957_; 
v_key_942_ = lean_ctor_get(v_a_941_, 0);
v_value_943_ = lean_ctor_get(v_a_941_, 1);
v_tail_944_ = lean_ctor_get(v_a_941_, 2);
v_isSharedCheck_957_ = !lean_is_exclusive(v_a_941_);
if (v_isSharedCheck_957_ == 0)
{
v___x_946_ = v_a_941_;
v_isShared_947_ = v_isSharedCheck_957_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_tail_944_);
lean_inc(v_value_943_);
lean_inc(v_key_942_);
lean_dec(v_a_941_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_957_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
uint8_t v___x_948_; 
v___x_948_ = lean_nat_dec_eq(v_key_942_, v_varIdx_939_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_950_ = lean_int_dec_eq(v_value_943_, v___x_949_);
if (v___x_950_ == 0)
{
lean_object* v___x_952_; 
if (v_isShared_947_ == 0)
{
lean_ctor_set(v___x_946_, 2, v_acc_940_);
v___x_952_ = v___x_946_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v_key_942_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v_value_943_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v_acc_940_);
v___x_952_ = v_reuseFailAlloc_954_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
v_acc_940_ = v___x_952_;
v_a_941_ = v_tail_944_;
goto _start;
}
}
else
{
lean_del_object(v___x_946_);
lean_dec(v_value_943_);
lean_dec(v_key_942_);
v_a_941_ = v_tail_944_;
goto _start;
}
}
else
{
lean_del_object(v___x_946_);
lean_dec(v_value_943_);
lean_dec(v_key_942_);
v_a_941_ = v_tail_944_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__7___boxed(lean_object* v_varIdx_958_, lean_object* v_acc_959_, lean_object* v_a_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__7(v_varIdx_958_, v_acc_959_, v_a_960_);
lean_dec(v_varIdx_958_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__8(lean_object* v_varIdx_962_, size_t v_sz_963_, size_t v_i_964_, lean_object* v_bs_965_){
_start:
{
uint8_t v___x_966_; 
v___x_966_ = lean_usize_dec_lt(v_i_964_, v_sz_963_);
if (v___x_966_ == 0)
{
return v_bs_965_;
}
else
{
lean_object* v_v_967_; lean_object* v___x_968_; lean_object* v_bs_x27_969_; lean_object* v___x_970_; lean_object* v___x_971_; size_t v___x_972_; size_t v___x_973_; lean_object* v___x_974_; 
v_v_967_ = lean_array_uget(v_bs_965_, v_i_964_);
v___x_968_ = lean_unsigned_to_nat(0u);
v_bs_x27_969_ = lean_array_uset(v_bs_965_, v_i_964_, v___x_968_);
v___x_970_ = lean_box(0);
v___x_971_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__7(v_varIdx_962_, v___x_970_, v_v_967_);
v___x_972_ = ((size_t)1ULL);
v___x_973_ = lean_usize_add(v_i_964_, v___x_972_);
v___x_974_ = lean_array_uset(v_bs_x27_969_, v_i_964_, v___x_971_);
v_i_964_ = v___x_973_;
v_bs_965_ = v___x_974_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__8___boxed(lean_object* v_varIdx_976_, lean_object* v_sz_977_, lean_object* v_i_978_, lean_object* v_bs_979_){
_start:
{
size_t v_sz_boxed_980_; size_t v_i_boxed_981_; lean_object* v_res_982_; 
v_sz_boxed_980_ = lean_unbox_usize(v_sz_977_);
lean_dec(v_sz_977_);
v_i_boxed_981_ = lean_unbox_usize(v_i_978_);
lean_dec(v_i_978_);
v_res_982_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__8(v_varIdx_976_, v_sz_boxed_980_, v_i_boxed_981_, v_bs_979_);
lean_dec(v_varIdx_976_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5(lean_object* v_varIdx_983_, lean_object* v_m_984_){
_start:
{
lean_object* v_buckets_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_1012_; 
v_buckets_985_ = lean_ctor_get(v_m_984_, 1);
v_isSharedCheck_1012_ = !lean_is_exclusive(v_m_984_);
if (v_isSharedCheck_1012_ == 0)
{
lean_object* v_unused_1013_; 
v_unused_1013_ = lean_ctor_get(v_m_984_, 0);
lean_dec(v_unused_1013_);
v___x_987_ = v_m_984_;
v_isShared_988_ = v_isSharedCheck_1012_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_buckets_985_);
lean_dec(v_m_984_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_1012_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
size_t v_sz_989_; size_t v___x_990_; lean_object* v_newBuckets_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; 
v_sz_989_ = lean_array_size(v_buckets_985_);
v___x_990_ = ((size_t)0ULL);
v_newBuckets_991_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__8(v_varIdx_983_, v_sz_989_, v___x_990_, v_buckets_985_);
v___x_992_ = lean_unsigned_to_nat(0u);
v___x_993_ = lean_array_get_size(v_newBuckets_991_);
v___x_994_ = lean_nat_dec_lt(v___x_992_, v___x_993_);
if (v___x_994_ == 0)
{
lean_object* v___x_996_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_992_);
v___x_996_ = v___x_987_;
goto v_reusejp_995_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_newBuckets_991_);
v___x_996_ = v_reuseFailAlloc_997_;
goto v_reusejp_995_;
}
v_reusejp_995_:
{
return v___x_996_;
}
}
else
{
uint8_t v___x_998_; 
v___x_998_ = lean_nat_dec_le(v___x_993_, v___x_993_);
if (v___x_998_ == 0)
{
if (v___x_994_ == 0)
{
lean_object* v___x_1000_; 
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_992_);
v___x_1000_ = v___x_987_;
goto v_reusejp_999_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_newBuckets_991_);
v___x_1000_ = v_reuseFailAlloc_1001_;
goto v_reusejp_999_;
}
v_reusejp_999_:
{
return v___x_1000_;
}
}
else
{
size_t v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1005_; 
v___x_1002_ = lean_usize_of_nat(v___x_993_);
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(v_newBuckets_991_, v___x_990_, v___x_1002_, v___x_992_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_1003_);
v___x_1005_ = v___x_987_;
goto v_reusejp_1004_;
}
else
{
lean_object* v_reuseFailAlloc_1006_; 
v_reuseFailAlloc_1006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1006_, 0, v___x_1003_);
lean_ctor_set(v_reuseFailAlloc_1006_, 1, v_newBuckets_991_);
v___x_1005_ = v_reuseFailAlloc_1006_;
goto v_reusejp_1004_;
}
v_reusejp_1004_:
{
return v___x_1005_;
}
}
}
else
{
size_t v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1007_ = lean_usize_of_nat(v___x_993_);
v___x_1008_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(v_newBuckets_991_, v___x_990_, v___x_1007_, v___x_992_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_newBuckets_991_);
lean_ctor_set(v___x_987_, 0, v___x_1008_);
v___x_1010_ = v___x_987_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_newBuckets_991_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5___boxed(lean_object* v_varIdx_1014_, lean_object* v_m_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5(v_varIdx_1014_, v_m_1015_);
lean_dec(v_varIdx_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0_spec__1(lean_object* v_msg_1017_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = l_Int_instInhabited;
v___x_1019_ = lean_panic_fn_borrowed(v___x_1018_, v_msg_1017_);
return v___x_1019_;
}
}
static lean_object* _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1023_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__2));
v___x_1024_ = lean_unsigned_to_nat(11u);
v___x_1025_ = lean_unsigned_to_nat(163u);
v___x_1026_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__1));
v___x_1027_ = ((lean_object*)(l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__0));
v___x_1028_ = l_mkPanicMessageWithDecl(v___x_1027_, v___x_1026_, v___x_1025_, v___x_1024_, v___x_1023_);
return v___x_1028_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0(lean_object* v_a_1029_, lean_object* v_x_1030_){
_start:
{
if (lean_obj_tag(v_x_1030_) == 0)
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3);
v___x_1032_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0_spec__1(v___x_1031_);
return v___x_1032_;
}
else
{
lean_object* v_key_1033_; lean_object* v_value_1034_; lean_object* v_tail_1035_; uint8_t v___x_1036_; 
v_key_1033_ = lean_ctor_get(v_x_1030_, 0);
v_value_1034_ = lean_ctor_get(v_x_1030_, 1);
v_tail_1035_ = lean_ctor_get(v_x_1030_, 2);
v___x_1036_ = lean_nat_dec_eq(v_key_1033_, v_a_1029_);
if (v___x_1036_ == 0)
{
v_x_1030_ = v_tail_1035_;
goto _start;
}
else
{
lean_inc(v_value_1034_);
return v_value_1034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___boxed(lean_object* v_a_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v_res_1040_; 
v_res_1040_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0(v_a_1038_, v_x_1039_);
lean_dec(v_x_1039_);
lean_dec(v_a_1038_);
return v_res_1040_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0(lean_object* v_m_1041_, lean_object* v_a_1042_){
_start:
{
lean_object* v_buckets_1043_; lean_object* v___x_1044_; uint64_t v___x_1045_; uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v_fold_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; size_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; 
v_buckets_1043_ = lean_ctor_get(v_m_1041_, 1);
v___x_1044_ = lean_array_get_size(v_buckets_1043_);
v___x_1045_ = lean_uint64_of_nat(v_a_1042_);
v___x_1046_ = 32ULL;
v___x_1047_ = lean_uint64_shift_right(v___x_1045_, v___x_1046_);
v_fold_1048_ = lean_uint64_xor(v___x_1045_, v___x_1047_);
v___x_1049_ = 16ULL;
v___x_1050_ = lean_uint64_shift_right(v_fold_1048_, v___x_1049_);
v___x_1051_ = lean_uint64_xor(v_fold_1048_, v___x_1050_);
v___x_1052_ = lean_uint64_to_usize(v___x_1051_);
v___x_1053_ = lean_usize_of_nat(v___x_1044_);
v___x_1054_ = ((size_t)1ULL);
v___x_1055_ = lean_usize_sub(v___x_1053_, v___x_1054_);
v___x_1056_ = lean_usize_land(v___x_1052_, v___x_1055_);
v___x_1057_ = lean_array_uget_borrowed(v_buckets_1043_, v___x_1056_);
v___x_1058_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0(v_a_1042_, v___x_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0___boxed(lean_object* v_m_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_res_1061_; 
v_res_1061_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0(v_m_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_m_1059_);
return v_res_1061_;
}
}
LEAN_EXPORT lean_object* l_Equation_subst(lean_object* v_fromEq_1062_, lean_object* v_toEq_1063_, lean_object* v_varIdx_1064_){
_start:
{
lean_object* v_coeffs_1065_; lean_object* v_const_1066_; lean_object* v_id_1067_; lean_object* v_coeffs_1068_; lean_object* v_const_1069_; lean_object* v___x_1071_; uint8_t v_isShared_1072_; uint8_t v_isSharedCheck_1088_; 
v_coeffs_1065_ = lean_ctor_get(v_fromEq_1062_, 1);
lean_inc_ref(v_coeffs_1065_);
v_const_1066_ = lean_ctor_get(v_fromEq_1062_, 2);
lean_inc(v_const_1066_);
lean_dec_ref(v_fromEq_1062_);
v_id_1067_ = lean_ctor_get(v_toEq_1063_, 0);
v_coeffs_1068_ = lean_ctor_get(v_toEq_1063_, 1);
v_const_1069_ = lean_ctor_get(v_toEq_1063_, 2);
v_isSharedCheck_1088_ = !lean_is_exclusive(v_toEq_1063_);
if (v_isSharedCheck_1088_ == 0)
{
v___x_1071_ = v_toEq_1063_;
v_isShared_1072_ = v_isSharedCheck_1088_;
goto v_resetjp_1070_;
}
else
{
lean_inc(v_const_1069_);
lean_inc(v_coeffs_1068_);
lean_inc(v_id_1067_);
lean_dec(v_toEq_1063_);
v___x_1071_ = lean_box(0);
v_isShared_1072_ = v_isSharedCheck_1088_;
goto v_resetjp_1070_;
}
v_resetjp_1070_:
{
lean_object* v_s_u2096_1073_; lean_object* v_buckets_1074_; lean_object* v_b_u2096_1075_; lean_object* v___f_1076_; lean_object* v_V__toEq_1077_; size_t v_sz_1078_; size_t v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1086_; 
v_s_u2096_1073_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0(v_coeffs_1065_, v_varIdx_1064_);
v_buckets_1074_ = lean_ctor_get(v_coeffs_1065_, 1);
lean_inc_ref(v_buckets_1074_);
v_b_u2096_1075_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0(v_coeffs_1068_, v_varIdx_1064_);
lean_inc(v_b_u2096_1075_);
lean_inc(v_s_u2096_1073_);
v___f_1076_ = lean_alloc_closure((void*)(l_Equation_subst___lam__0___boxed), 5, 3);
lean_closure_set(v___f_1076_, 0, v_coeffs_1065_);
lean_closure_set(v___f_1076_, 1, v_s_u2096_1073_);
lean_closure_set(v___f_1076_, 2, v_b_u2096_1075_);
v_V__toEq_1077_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v___f_1076_, v_coeffs_1068_);
v_sz_1078_ = lean_array_size(v_buckets_1074_);
v___x_1079_ = ((size_t)0ULL);
v___x_1080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_subst_spec__4(v_s_u2096_1073_, v_b_u2096_1075_, v_buckets_1074_, v_sz_1078_, v___x_1079_, v_V__toEq_1077_);
lean_dec_ref(v_buckets_1074_);
v___x_1081_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5(v_varIdx_1064_, v___x_1080_);
v___x_1082_ = lean_int_mul(v_b_u2096_1075_, v_s_u2096_1073_);
lean_dec(v_s_u2096_1073_);
lean_dec(v_b_u2096_1075_);
v___x_1083_ = lean_int_mul(v___x_1082_, v_const_1066_);
lean_dec(v_const_1066_);
lean_dec(v___x_1082_);
v___x_1084_ = lean_int_sub(v_const_1069_, v___x_1083_);
lean_dec(v___x_1083_);
lean_dec(v_const_1069_);
if (v_isShared_1072_ == 0)
{
lean_ctor_set(v___x_1071_, 2, v___x_1084_);
lean_ctor_set(v___x_1071_, 1, v___x_1081_);
v___x_1086_ = v___x_1071_;
goto v_reusejp_1085_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_id_1067_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v___x_1084_);
v___x_1086_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1085_;
}
v_reusejp_1085_:
{
return v___x_1086_;
}
}
}
}
LEAN_EXPORT lean_object* l_Equation_subst___boxed(lean_object* v_fromEq_1089_, lean_object* v_toEq_1090_, lean_object* v_varIdx_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l_Equation_subst(v_fromEq_1089_, v_toEq_1090_, v_varIdx_1091_);
lean_dec(v_varIdx_1091_);
return v_res_1092_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1(lean_object* v_00_u03b2_1093_, lean_object* v_m_1094_, lean_object* v_a_1095_){
_start:
{
uint8_t v___x_1096_; 
v___x_1096_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg(v_m_1094_, v_a_1095_);
return v___x_1096_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___boxed(lean_object* v_00_u03b2_1097_, lean_object* v_m_1098_, lean_object* v_a_1099_){
_start:
{
uint8_t v_res_1100_; lean_object* v_r_1101_; 
v_res_1100_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1(v_00_u03b2_1097_, v_m_1098_, v_a_1099_);
lean_dec(v_a_1099_);
lean_dec_ref(v_m_1098_);
v_r_1101_ = lean_box(v_res_1100_);
return v_r_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3(lean_object* v_00_u03b2_1102_, lean_object* v_m_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg(v_m_1103_, v_a_1104_);
return v___x_1105_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___boxed(lean_object* v_00_u03b2_1106_, lean_object* v_m_1107_, lean_object* v_a_1108_){
_start:
{
lean_object* v_res_1109_; 
v_res_1109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3(v_00_u03b2_1106_, v_m_1107_, v_a_1108_);
lean_dec(v_a_1108_);
lean_dec_ref(v_m_1107_);
return v_res_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4(lean_object* v_00_u03b2_1110_, lean_object* v_a_1111_, lean_object* v_x_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___redArg(v_a_1111_, v_x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4___boxed(lean_object* v_00_u03b2_1114_, lean_object* v_a_1115_, lean_object* v_x_1116_){
_start:
{
lean_object* v_res_1117_; 
v_res_1117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3_spec__4(v_00_u03b2_1114_, v_a_1115_, v_x_1116_);
lean_dec(v_x_1116_);
lean_dec(v_a_1115_);
return v_res_1117_;
}
}
static lean_object* _init_l_panic___at___00Equation_normalize_spec__1___closed__0(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = l_Int_instInhabited;
v___x_1119_ = lean_unsigned_to_nat(0u);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v___x_1118_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Equation_normalize_spec__1(lean_object* v_msg_1121_){
_start:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
v___x_1122_ = lean_obj_once(&l_panic___at___00Equation_normalize_spec__1___closed__0, &l_panic___at___00Equation_normalize_spec__1___closed__0_once, _init_l_panic___at___00Equation_normalize_spec__1___closed__0);
v___x_1123_ = lean_panic_fn_borrowed(v___x_1122_, v_msg_1121_);
return v___x_1123_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___redArg(lean_object* v_a_1124_, lean_object* v_a_1125_){
_start:
{
if (lean_obj_tag(v_a_1124_) == 0)
{
lean_object* v___x_1126_; 
v___x_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1126_, 0, v_a_1125_);
return v___x_1126_;
}
else
{
lean_object* v_key_1127_; lean_object* v_value_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
lean_dec_ref(v_a_1125_);
v_key_1127_ = lean_ctor_get(v_a_1124_, 0);
v_value_1128_ = lean_ctor_get(v_a_1124_, 1);
v___x_1129_ = lean_box(0);
lean_inc(v_value_1128_);
lean_inc(v_key_1127_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v_key_1127_);
lean_ctor_set(v___x_1130_, 1, v_value_1128_);
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
v___x_1132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
lean_ctor_set(v___x_1133_, 1, v___x_1129_);
v___x_1134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
return v___x_1134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___redArg___boxed(lean_object* v_a_1135_, lean_object* v_a_1136_){
_start:
{
lean_object* v_res_1137_; 
v_res_1137_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___redArg(v_a_1135_, v_a_1136_);
lean_dec(v_a_1135_);
return v_res_1137_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___redArg(lean_object* v_as_1138_, size_t v_sz_1139_, size_t v_i_1140_, lean_object* v_b_1141_){
_start:
{
uint8_t v___x_1142_; 
v___x_1142_ = lean_usize_dec_lt(v_i_1140_, v_sz_1139_);
if (v___x_1142_ == 0)
{
return v_b_1141_;
}
else
{
lean_object* v_a_1143_; lean_object* v___x_1144_; 
v_a_1143_ = lean_array_uget_borrowed(v_as_1138_, v_i_1140_);
v___x_1144_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___redArg(v_a_1143_, v_b_1141_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_object* v_a_1145_; 
v_a_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1145_);
lean_dec_ref_known(v___x_1144_, 1);
return v_a_1145_;
}
else
{
lean_object* v_a_1146_; size_t v___x_1147_; size_t v___x_1148_; 
v_a_1146_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1147_ = ((size_t)1ULL);
v___x_1148_ = lean_usize_add(v_i_1140_, v___x_1147_);
v_i_1140_ = v___x_1148_;
v_b_1141_ = v_a_1146_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___redArg___boxed(lean_object* v_as_1150_, lean_object* v_sz_1151_, lean_object* v_i_1152_, lean_object* v_b_1153_){
_start:
{
size_t v_sz_boxed_1154_; size_t v_i_boxed_1155_; lean_object* v_res_1156_; 
v_sz_boxed_1154_ = lean_unbox_usize(v_sz_1151_);
lean_dec(v_sz_1151_);
v_i_boxed_1155_ = lean_unbox_usize(v_i_1152_);
lean_dec(v_i_1152_);
v_res_1156_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___redArg(v_as_1150_, v_sz_boxed_1154_, v_i_boxed_1155_, v_b_1153_);
lean_dec_ref(v_as_1150_);
return v_res_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg(lean_object* v_x_1160_){
_start:
{
lean_object* v_buckets_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; size_t v_sz_1164_; size_t v___x_1165_; lean_object* v___x_1166_; lean_object* v_fst_1167_; 
v_buckets_1161_ = lean_ctor_get(v_x_1160_, 1);
v___x_1162_ = lean_box(0);
v___x_1163_ = ((lean_object*)(l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg___closed__0));
v_sz_1164_ = lean_array_size(v_buckets_1161_);
v___x_1165_ = ((size_t)0ULL);
v___x_1166_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___redArg(v_buckets_1161_, v_sz_1164_, v___x_1165_, v___x_1163_);
v_fst_1167_ = lean_ctor_get(v___x_1166_, 0);
lean_inc(v_fst_1167_);
lean_dec_ref(v___x_1166_);
if (lean_obj_tag(v_fst_1167_) == 0)
{
return v___x_1162_;
}
else
{
lean_object* v_val_1168_; 
v_val_1168_ = lean_ctor_get(v_fst_1167_, 0);
lean_inc(v_val_1168_);
lean_dec_ref_known(v_fst_1167_, 1);
return v_val_1168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg___boxed(lean_object* v_x_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg(v_x_1169_);
lean_dec_ref(v_x_1169_);
return v_res_1170_;
}
}
static lean_object* _init_l_Equation_normalize___closed__3(void){
_start:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; 
v___x_1174_ = ((lean_object*)(l_Equation_normalize___closed__2));
v___x_1175_ = lean_unsigned_to_nat(14u);
v___x_1176_ = lean_unsigned_to_nat(22u);
v___x_1177_ = ((lean_object*)(l_Equation_normalize___closed__1));
v___x_1178_ = ((lean_object*)(l_Equation_normalize___closed__0));
v___x_1179_ = l_mkPanicMessageWithDecl(v___x_1178_, v___x_1177_, v___x_1176_, v___x_1175_, v___x_1174_);
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_Equation_normalize(lean_object* v_e_1180_){
_start:
{
lean_object* v_coeffs_1181_; lean_object* v_id_1182_; lean_object* v_const_1183_; lean_object* v_size_1184_; lean_object* v___x_1185_; lean_object* v___y_1187_; uint8_t v___x_1194_; 
v_coeffs_1181_ = lean_ctor_get(v_e_1180_, 1);
v_id_1182_ = lean_ctor_get(v_e_1180_, 0);
v_const_1183_ = lean_ctor_get(v_e_1180_, 2);
v_size_1184_ = lean_ctor_get(v_coeffs_1181_, 0);
v___x_1185_ = lean_unsigned_to_nat(1u);
v___x_1194_ = lean_nat_dec_eq(v_size_1184_, v___x_1185_);
if (v___x_1194_ == 0)
{
return v_e_1180_;
}
else
{
lean_object* v___x_1195_; 
lean_inc(v_const_1183_);
lean_inc(v_id_1182_);
lean_inc_ref(v_coeffs_1181_);
lean_dec_ref(v_e_1180_);
v___x_1195_ = l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg(v_coeffs_1181_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1196_ = lean_obj_once(&l_Equation_normalize___closed__3, &l_Equation_normalize___closed__3_once, _init_l_Equation_normalize___closed__3);
v___x_1197_ = l_panic___at___00Equation_normalize_spec__1(v___x_1196_);
v___y_1187_ = v___x_1197_;
goto v___jp_1186_;
}
else
{
lean_object* v_val_1198_; 
v_val_1198_ = lean_ctor_get(v___x_1195_, 0);
lean_inc(v_val_1198_);
lean_dec_ref_known(v___x_1195_, 1);
v___y_1187_ = v_val_1198_;
goto v___jp_1186_;
}
}
v___jp_1186_:
{
lean_object* v_fst_1188_; lean_object* v_snd_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v_fst_1188_ = lean_ctor_get(v___y_1187_, 0);
lean_inc(v_fst_1188_);
v_snd_1189_ = lean_ctor_get(v___y_1187_, 1);
lean_inc(v_snd_1189_);
lean_dec_ref(v___y_1187_);
v___x_1190_ = lean_obj_once(&l_Int_roundedDiv___closed__2, &l_Int_roundedDiv___closed__2_once, _init_l_Int_roundedDiv___closed__2);
v___x_1191_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_coeffs_1181_, v_fst_1188_, v___x_1190_);
v___x_1192_ = lean_int_ediv(v_const_1183_, v_snd_1189_);
lean_dec(v_snd_1189_);
lean_dec(v_const_1183_);
v___x_1193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1193_, 0, v_id_1182_);
lean_ctor_set(v___x_1193_, 1, v___x_1191_);
lean_ctor_set(v___x_1193_, 2, v___x_1192_);
return v___x_1193_;
}
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0(lean_object* v_00_u03b2_1199_, lean_object* v_x_1200_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___redArg(v_x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0___boxed(lean_object* v_00_u03b2_1202_, lean_object* v_x_1203_){
_start:
{
lean_object* v_res_1204_; 
v_res_1204_ = l_Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0(v_00_u03b2_1202_, v_x_1203_);
lean_dec_ref(v_x_1203_);
return v_res_1204_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0(lean_object* v_00_u03b2_1205_, lean_object* v_a_1206_, lean_object* v_a_1207_){
_start:
{
lean_object* v___x_1208_; 
v___x_1208_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___redArg(v_a_1206_, v_a_1207_);
return v___x_1208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1209_, lean_object* v_a_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v_res_1212_; 
v_res_1212_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__0(v_00_u03b2_1209_, v_a_1210_, v_a_1211_);
lean_dec(v_a_1210_);
return v_res_1212_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1(lean_object* v_00_u03b2_1213_, lean_object* v_as_1214_, size_t v_sz_1215_, size_t v_i_1216_, lean_object* v_b_1217_){
_start:
{
lean_object* v___x_1218_; 
v___x_1218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___redArg(v_as_1214_, v_sz_1215_, v_i_1216_, v_b_1217_);
return v___x_1218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1219_, lean_object* v_as_1220_, lean_object* v_sz_1221_, lean_object* v_i_1222_, lean_object* v_b_1223_){
_start:
{
size_t v_sz_boxed_1224_; size_t v_i_boxed_1225_; lean_object* v_res_1226_; 
v_sz_boxed_1224_ = lean_unbox_usize(v_sz_1221_);
lean_dec(v_sz_1221_);
v_i_boxed_1225_ = lean_unbox_usize(v_i_1222_);
lean_dec(v_i_1222_);
v_res_1226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_HashMap_getAny_x3f___at___00Equation_normalize_spec__0_spec__1(v_00_u03b2_1219_, v_as_1220_, v_sz_boxed_1224_, v_i_boxed_1225_, v_b_1223_);
lean_dec_ref(v_as_1220_);
return v_res_1226_;
}
}
LEAN_EXPORT lean_object* l_Equation_invert___lam__0(lean_object* v_x_1227_, lean_object* v_coeff_1228_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; 
v___x_1229_ = lean_obj_once(&l_Int_roundedDiv___closed__3, &l_Int_roundedDiv___closed__3_once, _init_l_Int_roundedDiv___closed__3);
v___x_1230_ = lean_int_mul(v___x_1229_, v_coeff_1228_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l_Equation_invert___lam__0___boxed(lean_object* v_x_1231_, lean_object* v_coeff_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_Equation_invert___lam__0(v_x_1231_, v_coeff_1232_);
lean_dec(v_coeff_1232_);
lean_dec(v_x_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_Equation_invert(lean_object* v_e_1235_){
_start:
{
lean_object* v_id_1236_; lean_object* v_coeffs_1237_; lean_object* v_const_1238_; lean_object* v___x_1240_; uint8_t v_isShared_1241_; uint8_t v_isSharedCheck_1249_; 
v_id_1236_ = lean_ctor_get(v_e_1235_, 0);
v_coeffs_1237_ = lean_ctor_get(v_e_1235_, 1);
v_const_1238_ = lean_ctor_get(v_e_1235_, 2);
v_isSharedCheck_1249_ = !lean_is_exclusive(v_e_1235_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1240_ = v_e_1235_;
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
else
{
lean_inc(v_const_1238_);
lean_inc(v_coeffs_1237_);
lean_inc(v_id_1236_);
lean_dec(v_e_1235_);
v___x_1240_ = lean_box(0);
v_isShared_1241_ = v_isSharedCheck_1249_;
goto v_resetjp_1239_;
}
v_resetjp_1239_:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___f_1242_ = ((lean_object*)(l_Equation_invert___closed__0));
v___x_1243_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v___f_1242_, v_coeffs_1237_);
v___x_1244_ = lean_obj_once(&l_Int_roundedDiv___closed__3, &l_Int_roundedDiv___closed__3_once, _init_l_Int_roundedDiv___closed__3);
v___x_1245_ = lean_int_mul(v___x_1244_, v_const_1238_);
lean_dec(v_const_1238_);
if (v_isShared_1241_ == 0)
{
lean_ctor_set(v___x_1240_, 2, v___x_1245_);
lean_ctor_set(v___x_1240_, 1, v___x_1243_);
v___x_1247_ = v___x_1240_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v_id_1236_);
lean_ctor_set(v_reuseFailAlloc_1248_, 1, v___x_1243_);
lean_ctor_set(v_reuseFailAlloc_1248_, 2, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg(lean_object* v_a_1250_, lean_object* v_x_1251_){
_start:
{
if (lean_obj_tag(v_x_1251_) == 0)
{
return v_x_1251_;
}
else
{
lean_object* v_key_1252_; lean_object* v_value_1253_; lean_object* v_tail_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1263_; 
v_key_1252_ = lean_ctor_get(v_x_1251_, 0);
v_value_1253_ = lean_ctor_get(v_x_1251_, 1);
v_tail_1254_ = lean_ctor_get(v_x_1251_, 2);
v_isSharedCheck_1263_ = !lean_is_exclusive(v_x_1251_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1256_ = v_x_1251_;
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_tail_1254_);
lean_inc(v_value_1253_);
lean_inc(v_key_1252_);
lean_dec(v_x_1251_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1263_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
uint8_t v___x_1258_; 
v___x_1258_ = lean_nat_dec_eq(v_key_1252_, v_a_1250_);
if (v___x_1258_ == 0)
{
lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1259_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg(v_a_1250_, v_tail_1254_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 2, v___x_1259_);
v___x_1261_ = v___x_1256_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_key_1252_);
lean_ctor_set(v_reuseFailAlloc_1262_, 1, v_value_1253_);
lean_ctor_set(v_reuseFailAlloc_1262_, 2, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
else
{
lean_del_object(v___x_1256_);
lean_dec(v_value_1253_);
lean_dec(v_key_1252_);
return v_tail_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg___boxed(lean_object* v_a_1264_, lean_object* v_x_1265_){
_start:
{
lean_object* v_res_1266_; 
v_res_1266_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg(v_a_1264_, v_x_1265_);
lean_dec(v_a_1264_);
return v_res_1266_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg(lean_object* v_m_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_size_1269_; lean_object* v_buckets_1270_; lean_object* v___x_1271_; uint64_t v___x_1272_; uint64_t v___x_1273_; uint64_t v___x_1274_; uint64_t v_fold_1275_; uint64_t v___x_1276_; uint64_t v___x_1277_; uint64_t v___x_1278_; size_t v___x_1279_; size_t v___x_1280_; size_t v___x_1281_; size_t v___x_1282_; size_t v___x_1283_; lean_object* v_bkt_1284_; uint8_t v___x_1285_; 
v_size_1269_ = lean_ctor_get(v_m_1267_, 0);
v_buckets_1270_ = lean_ctor_get(v_m_1267_, 1);
v___x_1271_ = lean_array_get_size(v_buckets_1270_);
v___x_1272_ = lean_uint64_of_nat(v_a_1268_);
v___x_1273_ = 32ULL;
v___x_1274_ = lean_uint64_shift_right(v___x_1272_, v___x_1273_);
v_fold_1275_ = lean_uint64_xor(v___x_1272_, v___x_1274_);
v___x_1276_ = 16ULL;
v___x_1277_ = lean_uint64_shift_right(v_fold_1275_, v___x_1276_);
v___x_1278_ = lean_uint64_xor(v_fold_1275_, v___x_1277_);
v___x_1279_ = lean_uint64_to_usize(v___x_1278_);
v___x_1280_ = lean_usize_of_nat(v___x_1271_);
v___x_1281_ = ((size_t)1ULL);
v___x_1282_ = lean_usize_sub(v___x_1280_, v___x_1281_);
v___x_1283_ = lean_usize_land(v___x_1279_, v___x_1282_);
v_bkt_1284_ = lean_array_uget_borrowed(v_buckets_1270_, v___x_1283_);
v___x_1285_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0_spec__1___redArg(v_a_1268_, v_bkt_1284_);
if (v___x_1285_ == 0)
{
return v_m_1267_;
}
else
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1298_; 
lean_inc(v_bkt_1284_);
lean_inc_ref(v_buckets_1270_);
lean_inc(v_size_1269_);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_m_1267_);
if (v_isSharedCheck_1298_ == 0)
{
lean_object* v_unused_1299_; lean_object* v_unused_1300_; 
v_unused_1299_ = lean_ctor_get(v_m_1267_, 1);
lean_dec(v_unused_1299_);
v_unused_1300_ = lean_ctor_get(v_m_1267_, 0);
lean_dec(v_unused_1300_);
v___x_1287_ = v_m_1267_;
v_isShared_1288_ = v_isSharedCheck_1298_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v_m_1267_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1298_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v_buckets_x27_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1289_ = lean_box(0);
v_buckets_x27_1290_ = lean_array_uset(v_buckets_1270_, v___x_1283_, v___x_1289_);
v___x_1291_ = lean_unsigned_to_nat(1u);
v___x_1292_ = lean_nat_sub(v_size_1269_, v___x_1291_);
lean_dec(v_size_1269_);
v___x_1293_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg(v_a_1268_, v_bkt_1284_);
v___x_1294_ = lean_array_uset(v_buckets_x27_1290_, v___x_1283_, v___x_1293_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1294_);
lean_ctor_set(v___x_1287_, 0, v___x_1292_);
v___x_1296_ = v___x_1287_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v___x_1292_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg___boxed(lean_object* v_m_1301_, lean_object* v_a_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg(v_m_1301_, v_a_1302_);
lean_dec(v_a_1302_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l_Equation_reorganizeFor(lean_object* v_e_1304_, lean_object* v_varIdx_1305_){
_start:
{
lean_object* v_id_1307_; lean_object* v_coeffs_1308_; lean_object* v_const_1309_; lean_object* v_id_1312_; lean_object* v_coeffs_1313_; lean_object* v_const_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1330_; 
v_id_1312_ = lean_ctor_get(v_e_1304_, 0);
v_coeffs_1313_ = lean_ctor_get(v_e_1304_, 1);
v_const_1314_ = lean_ctor_get(v_e_1304_, 2);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_e_1304_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1316_ = v_e_1304_;
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_const_1314_);
lean_inc(v_coeffs_1313_);
lean_inc(v_id_1312_);
lean_dec(v_e_1304_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1330_;
goto v_resetjp_1315_;
}
v___jp_1306_:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg(v_coeffs_1308_, v_varIdx_1305_);
v___x_1311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1311_, 0, v_id_1307_);
lean_ctor_set(v___x_1311_, 1, v___x_1310_);
lean_ctor_set(v___x_1311_, 2, v_const_1309_);
return v___x_1311_;
}
v_resetjp_1315_:
{
lean_object* v___f_1318_; lean_object* v_singletonCoeff_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; uint8_t v___x_1322_; 
v___f_1318_ = ((lean_object*)(l_Equation_invert___closed__0));
v_singletonCoeff_1319_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0(v_coeffs_1313_, v_varIdx_1305_);
v___x_1320_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v___f_1318_, v_coeffs_1313_);
v___x_1321_ = lean_obj_once(&l_Int_roundedDiv___closed__3, &l_Int_roundedDiv___closed__3_once, _init_l_Int_roundedDiv___closed__3);
v___x_1322_ = lean_int_dec_eq(v_singletonCoeff_1319_, v___x_1321_);
lean_dec(v_singletonCoeff_1319_);
if (v___x_1322_ == 0)
{
lean_del_object(v___x_1316_);
v_id_1307_ = v_id_1312_;
v_coeffs_1308_ = v___x_1320_;
v_const_1309_ = v_const_1314_;
goto v___jp_1306_;
}
else
{
lean_object* v_e_1324_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 1, v___x_1320_);
v_e_1324_ = v___x_1316_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_id_1312_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v___x_1320_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_const_1314_);
v_e_1324_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
lean_object* v_e_1325_; lean_object* v_id_1326_; lean_object* v_coeffs_1327_; lean_object* v_const_1328_; 
v_e_1325_ = l_Equation_invert(v_e_1324_);
v_id_1326_ = lean_ctor_get(v_e_1325_, 0);
lean_inc(v_id_1326_);
v_coeffs_1327_ = lean_ctor_get(v_e_1325_, 1);
lean_inc_ref(v_coeffs_1327_);
v_const_1328_ = lean_ctor_get(v_e_1325_, 2);
lean_inc(v_const_1328_);
lean_dec_ref(v_e_1325_);
v_id_1307_ = v_id_1326_;
v_coeffs_1308_ = v_coeffs_1327_;
v_const_1309_ = v_const_1328_;
goto v___jp_1306_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Equation_reorganizeFor___boxed(lean_object* v_e_1331_, lean_object* v_varIdx_1332_){
_start:
{
lean_object* v_res_1333_; 
v_res_1333_ = l_Equation_reorganizeFor(v_e_1331_, v_varIdx_1332_);
lean_dec(v_varIdx_1332_);
return v_res_1333_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0(lean_object* v_00_u03b2_1334_, lean_object* v_m_1335_, lean_object* v_a_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg(v_m_1335_, v_a_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___boxed(lean_object* v_00_u03b2_1338_, lean_object* v_m_1339_, lean_object* v_a_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0(v_00_u03b2_1338_, v_m_1339_, v_a_1340_);
lean_dec(v_a_1340_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0(lean_object* v_00_u03b2_1342_, lean_object* v_a_1343_, lean_object* v_x_1344_){
_start:
{
lean_object* v___x_1345_; 
v___x_1345_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___redArg(v_a_1343_, v_x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0___boxed(lean_object* v_00_u03b2_1346_, lean_object* v_a_1347_, lean_object* v_x_1348_){
_start:
{
lean_object* v_res_1349_; 
v_res_1349_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0_spec__0(v_00_u03b2_1346_, v_a_1347_, v_x_1348_);
lean_dec(v_a_1347_);
return v_res_1349_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0(lean_object* v_a_1353_, lean_object* v_a_1354_){
_start:
{
if (lean_obj_tag(v_a_1353_) == 0)
{
lean_object* v___x_1355_; 
v___x_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1355_, 0, v_a_1354_);
return v___x_1355_;
}
else
{
lean_object* v_key_1356_; lean_object* v_value_1357_; lean_object* v_tail_1358_; lean_object* v___x_1359_; lean_object* v___x_1366_; uint8_t v___x_1367_; 
lean_dec_ref(v_a_1354_);
v_key_1356_ = lean_ctor_get(v_a_1353_, 0);
v_value_1357_ = lean_ctor_get(v_a_1353_, 1);
v_tail_1358_ = lean_ctor_get(v_a_1353_, 2);
v___x_1359_ = lean_box(0);
v___x_1366_ = lean_obj_once(&l_Int_roundedDiv___closed__2, &l_Int_roundedDiv___closed__2_once, _init_l_Int_roundedDiv___closed__2);
v___x_1367_ = lean_int_dec_eq(v_value_1357_, v___x_1366_);
if (v___x_1367_ == 0)
{
lean_object* v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = lean_obj_once(&l_Int_roundedDiv___closed__3, &l_Int_roundedDiv___closed__3_once, _init_l_Int_roundedDiv___closed__3);
v___x_1369_ = lean_int_dec_eq(v_value_1357_, v___x_1368_);
if (v___x_1369_ == 0)
{
lean_object* v___x_1370_; 
v___x_1370_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0___closed__0));
v_a_1353_ = v_tail_1358_;
v_a_1354_ = v___x_1370_;
goto _start;
}
else
{
goto v___jp_1360_;
}
}
else
{
goto v___jp_1360_;
}
v___jp_1360_:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_inc(v_value_1357_);
lean_inc(v_key_1356_);
v___x_1361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1361_, 0, v_key_1356_);
lean_ctor_set(v___x_1361_, 1, v_value_1357_);
v___x_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1362_, 0, v___x_1361_);
v___x_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1363_, 0, v___x_1362_);
v___x_1364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1364_, 0, v___x_1363_);
lean_ctor_set(v___x_1364_, 1, v___x_1359_);
v___x_1365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0___boxed(lean_object* v_a_1372_, lean_object* v_a_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0(v_a_1372_, v_a_1373_);
lean_dec(v_a_1372_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findSingleton_x3f_spec__1(lean_object* v_as_1375_, size_t v_sz_1376_, size_t v_i_1377_, lean_object* v_b_1378_){
_start:
{
uint8_t v___x_1379_; 
v___x_1379_ = lean_usize_dec_lt(v_i_1377_, v_sz_1376_);
if (v___x_1379_ == 0)
{
return v_b_1378_;
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1381_; 
v_a_1380_ = lean_array_uget_borrowed(v_as_1375_, v_i_1377_);
v___x_1381_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0(v_a_1380_, v_b_1378_);
if (lean_obj_tag(v___x_1381_) == 0)
{
lean_object* v_a_1382_; 
v_a_1382_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1382_);
lean_dec_ref_known(v___x_1381_, 1);
return v_a_1382_;
}
else
{
lean_object* v_a_1383_; size_t v___x_1384_; size_t v___x_1385_; 
v_a_1383_ = lean_ctor_get(v___x_1381_, 0);
lean_inc(v_a_1383_);
lean_dec_ref_known(v___x_1381_, 1);
v___x_1384_ = ((size_t)1ULL);
v___x_1385_ = lean_usize_add(v_i_1377_, v___x_1384_);
v_i_1377_ = v___x_1385_;
v_b_1378_ = v_a_1383_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findSingleton_x3f_spec__1___boxed(lean_object* v_as_1387_, lean_object* v_sz_1388_, lean_object* v_i_1389_, lean_object* v_b_1390_){
_start:
{
size_t v_sz_boxed_1391_; size_t v_i_boxed_1392_; lean_object* v_res_1393_; 
v_sz_boxed_1391_ = lean_unbox_usize(v_sz_1388_);
lean_dec(v_sz_1388_);
v_i_boxed_1392_ = lean_unbox_usize(v_i_1389_);
lean_dec(v_i_1389_);
v_res_1393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findSingleton_x3f_spec__1(v_as_1387_, v_sz_boxed_1391_, v_i_boxed_1392_, v_b_1390_);
lean_dec_ref(v_as_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Equation_findSingleton_x3f(lean_object* v_e_1394_){
_start:
{
lean_object* v_coeffs_1395_; lean_object* v_buckets_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; size_t v_sz_1399_; size_t v___x_1400_; lean_object* v___x_1401_; lean_object* v_fst_1402_; 
v_coeffs_1395_ = lean_ctor_get(v_e_1394_, 1);
v_buckets_1396_ = lean_ctor_get(v_coeffs_1395_, 1);
v___x_1397_ = lean_box(0);
v___x_1398_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findSingleton_x3f_spec__0___closed__0));
v_sz_1399_ = lean_array_size(v_buckets_1396_);
v___x_1400_ = ((size_t)0ULL);
v___x_1401_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findSingleton_x3f_spec__1(v_buckets_1396_, v_sz_1399_, v___x_1400_, v___x_1398_);
v_fst_1402_ = lean_ctor_get(v___x_1401_, 0);
lean_inc(v_fst_1402_);
lean_dec_ref(v___x_1401_);
if (lean_obj_tag(v_fst_1402_) == 0)
{
return v___x_1397_;
}
else
{
lean_object* v_val_1403_; 
v_val_1403_ = lean_ctor_get(v_fst_1402_, 0);
lean_inc(v_val_1403_);
lean_dec_ref_known(v_fst_1402_, 1);
return v_val_1403_;
}
}
}
LEAN_EXPORT lean_object* l_Equation_findSingleton_x3f___boxed(lean_object* v_e_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Equation_findSingleton_x3f(v_e_1404_);
lean_dec_ref(v_e_1404_);
return v_res_1405_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findAbsMinimumCoeff_x3f_spec__0(lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
if (lean_obj_tag(v_a_1406_) == 0)
{
lean_object* v___x_1408_; 
v___x_1408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1408_, 0, v_a_1407_);
return v___x_1408_;
}
else
{
if (lean_obj_tag(v_a_1407_) == 0)
{
lean_object* v_key_1409_; lean_object* v_value_1410_; lean_object* v_tail_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; 
v_key_1409_ = lean_ctor_get(v_a_1406_, 0);
v_value_1410_ = lean_ctor_get(v_a_1406_, 1);
v_tail_1411_ = lean_ctor_get(v_a_1406_, 2);
lean_inc(v_value_1410_);
lean_inc(v_key_1409_);
v___x_1412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1412_, 0, v_key_1409_);
lean_ctor_set(v___x_1412_, 1, v_value_1410_);
v___x_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1412_);
v_a_1406_ = v_tail_1411_;
v_a_1407_ = v___x_1413_;
goto _start;
}
else
{
lean_object* v_val_1415_; lean_object* v_key_1416_; lean_object* v_value_1417_; lean_object* v_tail_1418_; lean_object* v_snd_1419_; lean_object* v___x_1421_; uint8_t v_isShared_1422_; uint8_t v_isSharedCheck_1439_; 
v_val_1415_ = lean_ctor_get(v_a_1407_, 0);
lean_inc(v_val_1415_);
v_key_1416_ = lean_ctor_get(v_a_1406_, 0);
v_value_1417_ = lean_ctor_get(v_a_1406_, 1);
v_tail_1418_ = lean_ctor_get(v_a_1406_, 2);
v_snd_1419_ = lean_ctor_get(v_val_1415_, 1);
v_isSharedCheck_1439_ = !lean_is_exclusive(v_val_1415_);
if (v_isSharedCheck_1439_ == 0)
{
lean_object* v_unused_1440_; 
v_unused_1440_ = lean_ctor_get(v_val_1415_, 0);
lean_dec(v_unused_1440_);
v___x_1421_ = v_val_1415_;
v_isShared_1422_ = v_isSharedCheck_1439_;
goto v_resetjp_1420_;
}
else
{
lean_inc(v_snd_1419_);
lean_dec(v_val_1415_);
v___x_1421_ = lean_box(0);
v_isShared_1422_ = v_isSharedCheck_1439_;
goto v_resetjp_1420_;
}
v_resetjp_1420_:
{
lean_object* v___x_1423_; lean_object* v___x_1424_; uint8_t v___x_1425_; 
v___x_1423_ = lean_nat_abs(v_value_1417_);
v___x_1424_ = lean_nat_abs(v_snd_1419_);
lean_dec(v_snd_1419_);
v___x_1425_ = lean_nat_dec_lt(v___x_1423_, v___x_1424_);
lean_dec(v___x_1424_);
lean_dec(v___x_1423_);
if (v___x_1425_ == 0)
{
lean_del_object(v___x_1421_);
v_a_1406_ = v_tail_1418_;
goto _start;
}
else
{
lean_object* v___x_1428_; uint8_t v_isShared_1429_; uint8_t v_isSharedCheck_1437_; 
v_isSharedCheck_1437_ = !lean_is_exclusive(v_a_1407_);
if (v_isSharedCheck_1437_ == 0)
{
lean_object* v_unused_1438_; 
v_unused_1438_ = lean_ctor_get(v_a_1407_, 0);
lean_dec(v_unused_1438_);
v___x_1428_ = v_a_1407_;
v_isShared_1429_ = v_isSharedCheck_1437_;
goto v_resetjp_1427_;
}
else
{
lean_dec(v_a_1407_);
v___x_1428_ = lean_box(0);
v_isShared_1429_ = v_isSharedCheck_1437_;
goto v_resetjp_1427_;
}
v_resetjp_1427_:
{
lean_object* v___x_1431_; 
lean_inc(v_value_1417_);
lean_inc(v_key_1416_);
if (v_isShared_1422_ == 0)
{
lean_ctor_set(v___x_1421_, 1, v_value_1417_);
lean_ctor_set(v___x_1421_, 0, v_key_1416_);
v___x_1431_ = v___x_1421_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v_key_1416_);
lean_ctor_set(v_reuseFailAlloc_1436_, 1, v_value_1417_);
v___x_1431_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1433_; 
if (v_isShared_1429_ == 0)
{
lean_ctor_set(v___x_1428_, 0, v___x_1431_);
v___x_1433_ = v___x_1428_;
goto v_reusejp_1432_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1431_);
v___x_1433_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1432_;
}
v_reusejp_1432_:
{
v_a_1406_ = v_tail_1418_;
v_a_1407_ = v___x_1433_;
goto _start;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findAbsMinimumCoeff_x3f_spec__0___boxed(lean_object* v_a_1441_, lean_object* v_a_1442_){
_start:
{
lean_object* v_res_1443_; 
v_res_1443_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findAbsMinimumCoeff_x3f_spec__0(v_a_1441_, v_a_1442_);
lean_dec(v_a_1441_);
return v_res_1443_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findAbsMinimumCoeff_x3f_spec__1(lean_object* v_as_1444_, size_t v_sz_1445_, size_t v_i_1446_, lean_object* v_b_1447_){
_start:
{
uint8_t v___x_1448_; 
v___x_1448_ = lean_usize_dec_lt(v_i_1446_, v_sz_1445_);
if (v___x_1448_ == 0)
{
return v_b_1447_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1450_; 
v_a_1449_ = lean_array_uget_borrowed(v_as_1444_, v_i_1446_);
v___x_1450_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00Equation_findAbsMinimumCoeff_x3f_spec__0(v_a_1449_, v_b_1447_);
if (lean_obj_tag(v___x_1450_) == 0)
{
lean_object* v_a_1451_; 
v_a_1451_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1451_);
lean_dec_ref_known(v___x_1450_, 1);
return v_a_1451_;
}
else
{
lean_object* v_a_1452_; size_t v___x_1453_; size_t v___x_1454_; 
v_a_1452_ = lean_ctor_get(v___x_1450_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1450_, 1);
v___x_1453_ = ((size_t)1ULL);
v___x_1454_ = lean_usize_add(v_i_1446_, v___x_1453_);
v_i_1446_ = v___x_1454_;
v_b_1447_ = v_a_1452_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findAbsMinimumCoeff_x3f_spec__1___boxed(lean_object* v_as_1456_, lean_object* v_sz_1457_, lean_object* v_i_1458_, lean_object* v_b_1459_){
_start:
{
size_t v_sz_boxed_1460_; size_t v_i_boxed_1461_; lean_object* v_res_1462_; 
v_sz_boxed_1460_ = lean_unbox_usize(v_sz_1457_);
lean_dec(v_sz_1457_);
v_i_boxed_1461_ = lean_unbox_usize(v_i_1458_);
lean_dec(v_i_1458_);
v_res_1462_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findAbsMinimumCoeff_x3f_spec__1(v_as_1456_, v_sz_boxed_1460_, v_i_boxed_1461_, v_b_1459_);
lean_dec_ref(v_as_1456_);
return v_res_1462_;
}
}
LEAN_EXPORT lean_object* l_Equation_findAbsMinimumCoeff_x3f(lean_object* v_e_1463_){
_start:
{
lean_object* v_coeffs_1464_; lean_object* v_buckets_1465_; lean_object* v_r_x3f_1466_; size_t v_sz_1467_; size_t v___x_1468_; lean_object* v___x_1469_; 
v_coeffs_1464_ = lean_ctor_get(v_e_1463_, 1);
v_buckets_1465_ = lean_ctor_get(v_coeffs_1464_, 1);
v_r_x3f_1466_ = lean_box(0);
v_sz_1467_ = lean_array_size(v_buckets_1465_);
v___x_1468_ = ((size_t)0ULL);
v___x_1469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Equation_findAbsMinimumCoeff_x3f_spec__1(v_buckets_1465_, v_sz_1467_, v___x_1468_, v_r_x3f_1466_);
return v___x_1469_;
}
}
LEAN_EXPORT lean_object* l_Equation_findAbsMinimumCoeff_x3f___boxed(lean_object* v_e_1470_){
_start:
{
lean_object* v_res_1471_; 
v_res_1471_ = l_Equation_findAbsMinimumCoeff_x3f(v_e_1470_);
lean_dec_ref(v_e_1470_);
return v_res_1471_;
}
}
static lean_object* _init_l_instInhabitedProblem_default___closed__0(void){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = lean_obj_once(&l_instInhabitedEquation_default___closed__1, &l_instInhabitedEquation_default___closed__1_once, _init_l_instInhabitedEquation_default___closed__1);
v___x_1474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v___x_1473_);
lean_ctor_set(v___x_1474_, 2, v___x_1472_);
lean_ctor_set(v___x_1474_, 3, v___x_1472_);
return v___x_1474_;
}
}
static lean_object* _init_l_instInhabitedProblem_default(void){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_obj_once(&l_instInhabitedProblem_default___closed__0, &l_instInhabitedProblem_default___closed__0_once, _init_l_instInhabitedProblem_default___closed__0);
return v___x_1475_;
}
}
static lean_object* _init_l_instInhabitedProblem(void){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = l_instInhabitedProblem_default;
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__0___redArg(lean_object* v_f_1477_, lean_object* v_x_1478_, lean_object* v_x_1479_){
_start:
{
if (lean_obj_tag(v_x_1479_) == 0)
{
lean_object* v___x_1480_; 
lean_dec_ref(v_f_1477_);
v___x_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1480_, 0, v_x_1478_);
return v___x_1480_;
}
else
{
lean_object* v_key_1481_; lean_object* v_value_1482_; lean_object* v_tail_1483_; lean_object* v___x_1484_; 
v_key_1481_ = lean_ctor_get(v_x_1479_, 0);
lean_inc(v_key_1481_);
v_value_1482_ = lean_ctor_get(v_x_1479_, 1);
lean_inc(v_value_1482_);
v_tail_1483_ = lean_ctor_get(v_x_1479_, 2);
lean_inc(v_tail_1483_);
lean_dec_ref_known(v_x_1479_, 3);
lean_inc_ref(v_f_1477_);
v___x_1484_ = lean_apply_1(v_f_1477_, v_value_1482_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v___x_1485_; 
lean_dec(v_tail_1483_);
lean_dec(v_key_1481_);
lean_dec_ref(v_x_1478_);
lean_dec_ref(v_f_1477_);
v___x_1485_ = lean_box(0);
return v___x_1485_;
}
else
{
lean_object* v_val_1486_; lean_object* v___x_1487_; 
v_val_1486_ = lean_ctor_get(v___x_1484_, 0);
lean_inc(v_val_1486_);
lean_dec_ref_known(v___x_1484_, 1);
v___x_1487_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_x_1478_, v_key_1481_, v_val_1486_);
v_x_1478_ = v___x_1487_;
v_x_1479_ = v_tail_1483_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg(lean_object* v_f_1489_, lean_object* v_as_1490_, size_t v_i_1491_, size_t v_stop_1492_, lean_object* v_b_1493_){
_start:
{
uint8_t v___x_1494_; 
v___x_1494_ = lean_usize_dec_eq(v_i_1491_, v_stop_1492_);
if (v___x_1494_ == 0)
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_array_uget_borrowed(v_as_1490_, v_i_1491_);
lean_inc(v___x_1495_);
lean_inc_ref(v_f_1489_);
v___x_1496_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__0___redArg(v_f_1489_, v_b_1493_, v___x_1495_);
if (lean_obj_tag(v___x_1496_) == 0)
{
lean_dec_ref(v_f_1489_);
return v___x_1496_;
}
else
{
lean_object* v_val_1497_; size_t v___x_1498_; size_t v___x_1499_; 
v_val_1497_ = lean_ctor_get(v___x_1496_, 0);
lean_inc(v_val_1497_);
lean_dec_ref_known(v___x_1496_, 1);
v___x_1498_ = ((size_t)1ULL);
v___x_1499_ = lean_usize_add(v_i_1491_, v___x_1498_);
v_i_1491_ = v___x_1499_;
v_b_1493_ = v_val_1497_;
goto _start;
}
}
else
{
lean_object* v___x_1501_; 
lean_dec_ref(v_f_1489_);
v___x_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1501_, 0, v_b_1493_);
return v___x_1501_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg___boxed(lean_object* v_f_1502_, lean_object* v_as_1503_, lean_object* v_i_1504_, lean_object* v_stop_1505_, lean_object* v_b_1506_){
_start:
{
size_t v_i_boxed_1507_; size_t v_stop_boxed_1508_; lean_object* v_res_1509_; 
v_i_boxed_1507_ = lean_unbox_usize(v_i_1504_);
lean_dec(v_i_1504_);
v_stop_boxed_1508_ = lean_unbox_usize(v_stop_1505_);
lean_dec(v_stop_1505_);
v_res_1509_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg(v_f_1502_, v_as_1503_, v_i_boxed_1507_, v_stop_boxed_1508_, v_b_1506_);
lean_dec_ref(v_as_1503_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0___redArg(lean_object* v_f_1510_, lean_object* v_xs_1511_){
_start:
{
lean_object* v_size_1512_; lean_object* v_buckets_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1539_; 
v_size_1512_ = lean_ctor_get(v_xs_1511_, 0);
v_buckets_1513_ = lean_ctor_get(v_xs_1511_, 1);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_xs_1511_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1515_ = v_xs_1511_;
v_isShared_1516_ = v_isSharedCheck_1539_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_buckets_1513_);
lean_inc(v_size_1512_);
lean_dec(v_xs_1511_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1539_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1526_; 
v___x_1517_ = lean_unsigned_to_nat(0u);
v___x_1518_ = lean_unsigned_to_nat(4u);
v___x_1519_ = lean_nat_mul(v_size_1512_, v___x_1518_);
lean_dec(v_size_1512_);
v___x_1520_ = lean_unsigned_to_nat(3u);
v___x_1521_ = lean_nat_div(v___x_1519_, v___x_1520_);
lean_dec(v___x_1519_);
v___x_1522_ = l_Nat_nextPowerOfTwo(v___x_1521_);
lean_dec(v___x_1521_);
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_mk_array(v___x_1522_, v___x_1523_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1524_);
lean_ctor_set(v___x_1515_, 0, v___x_1517_);
v___x_1526_ = v___x_1515_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1524_);
v___x_1526_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
lean_object* v___x_1527_; uint8_t v___x_1528_; 
v___x_1527_ = lean_array_get_size(v_buckets_1513_);
v___x_1528_ = lean_nat_dec_lt(v___x_1517_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; 
lean_dec_ref(v_buckets_1513_);
lean_dec_ref(v_f_1510_);
v___x_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1529_, 0, v___x_1526_);
return v___x_1529_;
}
else
{
uint8_t v___x_1530_; 
v___x_1530_ = lean_nat_dec_le(v___x_1527_, v___x_1527_);
if (v___x_1530_ == 0)
{
if (v___x_1528_ == 0)
{
lean_object* v___x_1531_; 
lean_dec_ref(v_buckets_1513_);
lean_dec_ref(v_f_1510_);
v___x_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1526_);
return v___x_1531_;
}
else
{
size_t v___x_1532_; size_t v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = ((size_t)0ULL);
v___x_1533_ = lean_usize_of_nat(v___x_1527_);
v___x_1534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg(v_f_1510_, v_buckets_1513_, v___x_1532_, v___x_1533_, v___x_1526_);
lean_dec_ref(v_buckets_1513_);
return v___x_1534_;
}
}
else
{
size_t v___x_1535_; size_t v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = ((size_t)0ULL);
v___x_1536_ = lean_usize_of_nat(v___x_1527_);
v___x_1537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg(v_f_1510_, v_buckets_1513_, v___x_1535_, v___x_1536_, v___x_1526_);
lean_dec_ref(v_buckets_1513_);
return v___x_1537_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_preprocess_x3f(lean_object* v_eqs_1541_){
_start:
{
lean_object* v___f_1542_; lean_object* v___x_1543_; 
v___f_1542_ = ((lean_object*)(l_preprocess_x3f___closed__0));
v___x_1543_ = l_Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0___redArg(v___f_1542_, v_eqs_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0(lean_object* v_00_u03b2_1544_, lean_object* v_00_u03b3_1545_, lean_object* v_f_1546_, lean_object* v_xs_1547_){
_start:
{
lean_object* v___x_1548_; 
v___x_1548_ = l_Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0___redArg(v_f_1546_, v_xs_1547_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__0(lean_object* v_00_u03b2_1549_, lean_object* v_00_u03b3_1550_, lean_object* v_f_1551_, lean_object* v_x_1552_, lean_object* v_x_1553_){
_start:
{
lean_object* v___x_1554_; 
v___x_1554_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__0___redArg(v_f_1551_, v_x_1552_, v_x_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1(lean_object* v_00_u03b2_1555_, lean_object* v_00_u03b3_1556_, lean_object* v_f_1557_, lean_object* v_as_1558_, size_t v_i_1559_, size_t v_stop_1560_, lean_object* v_b_1561_){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___redArg(v_f_1557_, v_as_1558_, v_i_1559_, v_stop_1560_, v_b_1561_);
return v___x_1562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1___boxed(lean_object* v_00_u03b2_1563_, lean_object* v_00_u03b3_1564_, lean_object* v_f_1565_, lean_object* v_as_1566_, lean_object* v_i_1567_, lean_object* v_stop_1568_, lean_object* v_b_1569_){
_start:
{
size_t v_i_boxed_1570_; size_t v_stop_boxed_1571_; lean_object* v_res_1572_; 
v_i_boxed_1570_ = lean_unbox_usize(v_i_1567_);
lean_dec(v_i_1567_);
v_stop_boxed_1571_ = lean_unbox_usize(v_stop_1568_);
lean_dec(v_stop_1568_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_HashMap_mapValsM___at___00preprocess_x3f_spec__0_spec__1(v_00_u03b2_1563_, v_00_u03b3_1564_, v_f_1565_, v_as_1566_, v_i_boxed_1570_, v_stop_boxed_1571_, v_b_1569_);
lean_dec_ref(v_as_1566_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingleton_spec__1(lean_object* v_varIdx_1573_, lean_object* v_a_1574_, lean_object* v_a_1575_){
_start:
{
if (lean_obj_tag(v_a_1574_) == 0)
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1576_, 0, v_a_1575_);
return v___x_1576_;
}
else
{
lean_object* v_value_1577_; lean_object* v_key_1578_; lean_object* v_tail_1579_; lean_object* v_coeffs_1580_; uint8_t v___x_1581_; 
v_value_1577_ = lean_ctor_get(v_a_1574_, 1);
lean_inc(v_value_1577_);
v_key_1578_ = lean_ctor_get(v_a_1574_, 0);
lean_inc(v_key_1578_);
v_tail_1579_ = lean_ctor_get(v_a_1574_, 2);
lean_inc(v_tail_1579_);
lean_dec_ref_known(v_a_1574_, 3);
v_coeffs_1580_ = lean_ctor_get(v_value_1577_, 1);
lean_inc_ref(v_coeffs_1580_);
lean_dec(v_value_1577_);
v___x_1581_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Equation_subst_spec__1___redArg(v_coeffs_1580_, v_varIdx_1573_);
lean_dec_ref(v_coeffs_1580_);
if (v___x_1581_ == 0)
{
lean_dec(v_key_1578_);
v_a_1574_ = v_tail_1579_;
goto _start;
}
else
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_array_push(v_a_1575_, v_key_1578_);
v_a_1574_ = v_tail_1579_;
v_a_1575_ = v___x_1583_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingleton_spec__1___boxed(lean_object* v_varIdx_1585_, lean_object* v_a_1586_, lean_object* v_a_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingleton_spec__1(v_varIdx_1585_, v_a_1586_, v_a_1587_);
lean_dec(v_varIdx_1585_);
return v_res_1588_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__2(lean_object* v_varIdx_1589_, lean_object* v_as_1590_, size_t v_sz_1591_, size_t v_i_1592_, lean_object* v_b_1593_){
_start:
{
uint8_t v___x_1594_; 
v___x_1594_ = lean_usize_dec_lt(v_i_1592_, v_sz_1591_);
if (v___x_1594_ == 0)
{
return v_b_1593_;
}
else
{
lean_object* v_a_1595_; lean_object* v___x_1596_; 
v_a_1595_ = lean_array_uget_borrowed(v_as_1590_, v_i_1592_);
lean_inc(v_a_1595_);
v___x_1596_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingleton_spec__1(v_varIdx_1589_, v_a_1595_, v_b_1593_);
if (lean_obj_tag(v___x_1596_) == 0)
{
lean_object* v_a_1597_; 
v_a_1597_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1597_);
lean_dec_ref_known(v___x_1596_, 1);
return v_a_1597_;
}
else
{
lean_object* v_a_1598_; size_t v___x_1599_; size_t v___x_1600_; 
v_a_1598_ = lean_ctor_get(v___x_1596_, 0);
lean_inc(v_a_1598_);
lean_dec_ref_known(v___x_1596_, 1);
v___x_1599_ = ((size_t)1ULL);
v___x_1600_ = lean_usize_add(v_i_1592_, v___x_1599_);
v_i_1592_ = v___x_1600_;
v_b_1593_ = v_a_1598_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__2___boxed(lean_object* v_varIdx_1602_, lean_object* v_as_1603_, lean_object* v_sz_1604_, lean_object* v_i_1605_, lean_object* v_b_1606_){
_start:
{
size_t v_sz_boxed_1607_; size_t v_i_boxed_1608_; lean_object* v_res_1609_; 
v_sz_boxed_1607_ = lean_unbox_usize(v_sz_1604_);
lean_dec(v_sz_1604_);
v_i_boxed_1608_ = lean_unbox_usize(v_i_1605_);
lean_dec(v_i_1605_);
v_res_1609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__2(v_varIdx_1602_, v_as_1603_, v_sz_boxed_1607_, v_i_boxed_1608_, v_b_1606_);
lean_dec_ref(v_as_1603_);
lean_dec(v_varIdx_1602_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___lam__0(lean_object* v_singletonEq_1610_, lean_object* v_varIdx_1611_, lean_object* v_eq_1612_){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; 
v___x_1613_ = l_Equation_subst(v_singletonEq_1610_, v_eq_1612_, v_varIdx_1611_);
v___x_1614_ = l_Equation_normalize(v___x_1613_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___lam__0___boxed(lean_object* v_singletonEq_1615_, lean_object* v_varIdx_1616_, lean_object* v_eq_1617_){
_start:
{
lean_object* v_res_1618_; 
v_res_1618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___lam__0(v_singletonEq_1615_, v_varIdx_1616_, v_eq_1617_);
lean_dec(v_varIdx_1616_);
return v_res_1618_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1_spec__5(lean_object* v_msg_1619_){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; 
v___x_1620_ = l_instInhabitedEquation_default;
v___x_1621_ = lean_panic_fn_borrowed(v___x_1620_, v_msg_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1(lean_object* v_a_1622_, lean_object* v_x_1623_){
_start:
{
if (lean_obj_tag(v_x_1623_) == 0)
{
lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1624_ = lean_obj_once(&l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3, &l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3_once, _init_l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0___closed__3);
v___x_1625_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1_spec__5(v___x_1624_);
return v___x_1625_;
}
else
{
lean_object* v_key_1626_; lean_object* v_value_1627_; lean_object* v_tail_1628_; uint8_t v___x_1629_; 
v_key_1626_ = lean_ctor_get(v_x_1623_, 0);
v_value_1627_ = lean_ctor_get(v_x_1623_, 1);
v_tail_1628_ = lean_ctor_get(v_x_1623_, 2);
v___x_1629_ = lean_nat_dec_eq(v_key_1626_, v_a_1622_);
if (v___x_1629_ == 0)
{
v_x_1623_ = v_tail_1628_;
goto _start;
}
else
{
lean_inc(v_value_1627_);
return v_value_1627_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1___boxed(lean_object* v_a_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1(v_a_1631_, v_x_1632_);
lean_dec(v_x_1632_);
lean_dec(v_a_1631_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0(lean_object* v_m_1634_, lean_object* v_a_1635_){
_start:
{
lean_object* v_buckets_1636_; lean_object* v___x_1637_; uint64_t v___x_1638_; uint64_t v___x_1639_; uint64_t v___x_1640_; uint64_t v_fold_1641_; uint64_t v___x_1642_; uint64_t v___x_1643_; uint64_t v___x_1644_; size_t v___x_1645_; size_t v___x_1646_; size_t v___x_1647_; size_t v___x_1648_; size_t v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
v_buckets_1636_ = lean_ctor_get(v_m_1634_, 1);
v___x_1637_ = lean_array_get_size(v_buckets_1636_);
v___x_1638_ = lean_uint64_of_nat(v_a_1635_);
v___x_1639_ = 32ULL;
v___x_1640_ = lean_uint64_shift_right(v___x_1638_, v___x_1639_);
v_fold_1641_ = lean_uint64_xor(v___x_1638_, v___x_1640_);
v___x_1642_ = 16ULL;
v___x_1643_ = lean_uint64_shift_right(v_fold_1641_, v___x_1642_);
v___x_1644_ = lean_uint64_xor(v_fold_1641_, v___x_1643_);
v___x_1645_ = lean_uint64_to_usize(v___x_1644_);
v___x_1646_ = lean_usize_of_nat(v___x_1637_);
v___x_1647_ = ((size_t)1ULL);
v___x_1648_ = lean_usize_sub(v___x_1646_, v___x_1647_);
v___x_1649_ = lean_usize_land(v___x_1645_, v___x_1648_);
v___x_1650_ = lean_array_uget_borrowed(v_buckets_1636_, v___x_1649_);
v___x_1651_ = l_Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1(v_a_1635_, v___x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0___boxed(lean_object* v_m_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0(v_m_1652_, v_a_1653_);
lean_dec(v_a_1653_);
lean_dec_ref(v_m_1652_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0(lean_object* v_xs_1655_, lean_object* v_k_1656_, lean_object* v_f_1657_){
_start:
{
lean_object* v_v_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_v_1658_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0(v_xs_1655_, v_k_1656_);
v___x_1659_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg(v_xs_1655_, v_k_1656_);
v___x_1660_ = lean_apply_1(v_f_1657_, v_v_1658_);
v___x_1661_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v___x_1659_, v_k_1656_, v___x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3(lean_object* v_singletonEq_1662_, lean_object* v_varIdx_1663_, lean_object* v_as_1664_, size_t v_sz_1665_, size_t v_i_1666_, lean_object* v_b_1667_){
_start:
{
lean_object* v_a_1669_; uint8_t v___x_1673_; 
v___x_1673_ = lean_usize_dec_lt(v_i_1666_, v_sz_1665_);
if (v___x_1673_ == 0)
{
lean_dec(v_varIdx_1663_);
lean_dec_ref(v_singletonEq_1662_);
return v_b_1667_;
}
else
{
lean_object* v_id_1674_; lean_object* v_a_1675_; uint8_t v___x_1676_; 
v_id_1674_ = lean_ctor_get(v_singletonEq_1662_, 0);
v_a_1675_ = lean_array_uget_borrowed(v_as_1664_, v_i_1666_);
v___x_1676_ = lean_nat_dec_eq(v_a_1675_, v_id_1674_);
if (v___x_1676_ == 0)
{
lean_object* v___f_1677_; lean_object* v___x_1678_; 
lean_inc(v_varIdx_1663_);
lean_inc_ref(v_singletonEq_1662_);
v___f_1677_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___lam__0___boxed), 3, 2);
lean_closure_set(v___f_1677_, 0, v_singletonEq_1662_);
lean_closure_set(v___f_1677_, 1, v_varIdx_1663_);
lean_inc(v_a_1675_);
v___x_1678_ = l_Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0(v_b_1667_, v_a_1675_, v___f_1677_);
v_a_1669_ = v___x_1678_;
goto v___jp_1668_;
}
else
{
v_a_1669_ = v_b_1667_;
goto v___jp_1668_;
}
}
v___jp_1668_:
{
size_t v___x_1670_; size_t v___x_1671_; 
v___x_1670_ = ((size_t)1ULL);
v___x_1671_ = lean_usize_add(v_i_1666_, v___x_1670_);
v_i_1666_ = v___x_1671_;
v_b_1667_ = v_a_1669_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3___boxed(lean_object* v_singletonEq_1679_, lean_object* v_varIdx_1680_, lean_object* v_as_1681_, lean_object* v_sz_1682_, lean_object* v_i_1683_, lean_object* v_b_1684_){
_start:
{
size_t v_sz_boxed_1685_; size_t v_i_boxed_1686_; lean_object* v_res_1687_; 
v_sz_boxed_1685_ = lean_unbox_usize(v_sz_1682_);
lean_dec(v_sz_1682_);
v_i_boxed_1686_ = lean_unbox_usize(v_i_1683_);
lean_dec(v_i_1683_);
v_res_1687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3(v_singletonEq_1679_, v_varIdx_1680_, v_as_1681_, v_sz_boxed_1685_, v_i_boxed_1686_, v_b_1684_);
lean_dec_ref(v_as_1681_);
return v_res_1687_;
}
}
LEAN_EXPORT lean_object* l_eliminateSingleton(lean_object* v_p_1690_, lean_object* v_singletonEq_1691_, lean_object* v_varIdx_1692_){
_start:
{
lean_object* v_equations_1693_; lean_object* v_solvedEquations_1694_; lean_object* v_nEquations_1695_; lean_object* v_nVars_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1714_; 
v_equations_1693_ = lean_ctor_get(v_p_1690_, 0);
v_solvedEquations_1694_ = lean_ctor_get(v_p_1690_, 1);
v_nEquations_1695_ = lean_ctor_get(v_p_1690_, 2);
v_nVars_1696_ = lean_ctor_get(v_p_1690_, 3);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_p_1690_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1698_ = v_p_1690_;
v_isShared_1699_ = v_isSharedCheck_1714_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_nVars_1696_);
lean_inc(v_nEquations_1695_);
lean_inc(v_solvedEquations_1694_);
lean_inc(v_equations_1693_);
lean_dec(v_p_1690_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1714_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v_buckets_1700_; size_t v_sz_1701_; lean_object* v_id_1702_; lean_object* v_eqsWithVarIdx_1703_; size_t v___x_1704_; lean_object* v___x_1705_; size_t v_sz_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1712_; 
v_buckets_1700_ = lean_ctor_get(v_equations_1693_, 1);
v_sz_1701_ = lean_array_size(v_buckets_1700_);
v_id_1702_ = lean_ctor_get(v_singletonEq_1691_, 0);
v_eqsWithVarIdx_1703_ = ((lean_object*)(l_eliminateSingleton___closed__0));
v___x_1704_ = ((size_t)0ULL);
v___x_1705_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__2(v_varIdx_1692_, v_buckets_1700_, v_sz_1701_, v___x_1704_, v_eqsWithVarIdx_1703_);
v_sz_1706_ = lean_array_size(v___x_1705_);
lean_inc(v_varIdx_1692_);
lean_inc_ref(v_singletonEq_1691_);
v___x_1707_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingleton_spec__3(v_singletonEq_1691_, v_varIdx_1692_, v___x_1705_, v_sz_1706_, v___x_1704_, v_equations_1693_);
lean_dec_ref(v___x_1705_);
v___x_1708_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Equation_reorganizeFor_spec__0___redArg(v___x_1707_, v_id_1702_);
v___x_1709_ = l_Equation_reorganizeFor(v_singletonEq_1691_, v_varIdx_1692_);
v___x_1710_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_solvedEquations_1694_, v_varIdx_1692_, v___x_1709_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 1, v___x_1710_);
lean_ctor_set(v___x_1698_, 0, v___x_1708_);
v___x_1712_ = v___x_1698_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1708_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1710_);
lean_ctor_set(v_reuseFailAlloc_1713_, 2, v_nEquations_1695_);
lean_ctor_set(v_reuseFailAlloc_1713_, 3, v_nVars_1696_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingletons_spec__0(lean_object* v_a_1715_, lean_object* v_a_1716_){
_start:
{
if (lean_obj_tag(v_a_1715_) == 0)
{
lean_object* v___x_1717_; 
v___x_1717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1717_, 0, v_a_1716_);
return v___x_1717_;
}
else
{
lean_object* v_value_1718_; lean_object* v_tail_1719_; lean_object* v___x_1720_; 
v_value_1718_ = lean_ctor_get(v_a_1715_, 1);
v_tail_1719_ = lean_ctor_get(v_a_1715_, 2);
v___x_1720_ = l_Equation_findSingleton_x3f(v_value_1718_);
if (lean_obj_tag(v___x_1720_) == 0)
{
v_a_1715_ = v_tail_1719_;
goto _start;
}
else
{
lean_object* v_val_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1716_);
v_val_1722_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1724_ = v___x_1720_;
v_isShared_1725_ = v_isSharedCheck_1739_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_val_1722_);
lean_dec(v___x_1720_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1739_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_fst_1726_; lean_object* v___x_1728_; uint8_t v_isShared_1729_; uint8_t v_isSharedCheck_1737_; 
v_fst_1726_ = lean_ctor_get(v_val_1722_, 0);
v_isSharedCheck_1737_ = !lean_is_exclusive(v_val_1722_);
if (v_isSharedCheck_1737_ == 0)
{
lean_object* v_unused_1738_; 
v_unused_1738_ = lean_ctor_get(v_val_1722_, 1);
lean_dec(v_unused_1738_);
v___x_1728_ = v_val_1722_;
v_isShared_1729_ = v_isSharedCheck_1737_;
goto v_resetjp_1727_;
}
else
{
lean_inc(v_fst_1726_);
lean_dec(v_val_1722_);
v___x_1728_ = lean_box(0);
v_isShared_1729_ = v_isSharedCheck_1737_;
goto v_resetjp_1727_;
}
v_resetjp_1727_:
{
lean_object* v___x_1731_; 
lean_inc(v_value_1718_);
if (v_isShared_1729_ == 0)
{
lean_ctor_set(v___x_1728_, 1, v_fst_1726_);
lean_ctor_set(v___x_1728_, 0, v_value_1718_);
v___x_1731_ = v___x_1728_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_value_1718_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v_fst_1726_);
v___x_1731_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
lean_object* v___x_1733_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1731_);
v___x_1733_ = v___x_1724_;
goto v_reusejp_1732_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v___x_1731_);
v___x_1733_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1732_;
}
v_reusejp_1732_:
{
v_a_1715_ = v_tail_1719_;
v_a_1716_ = v___x_1733_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingletons_spec__0___boxed(lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v_res_1742_; 
v_res_1742_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingletons_spec__0(v_a_1740_, v_a_1741_);
lean_dec(v_a_1740_);
return v_res_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingletons_spec__1(lean_object* v_as_1743_, size_t v_sz_1744_, size_t v_i_1745_, lean_object* v_b_1746_){
_start:
{
uint8_t v___x_1747_; 
v___x_1747_ = lean_usize_dec_lt(v_i_1745_, v_sz_1744_);
if (v___x_1747_ == 0)
{
return v_b_1746_;
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1749_; 
v_a_1748_ = lean_array_uget_borrowed(v_as_1743_, v_i_1745_);
v___x_1749_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00eliminateSingletons_spec__0(v_a_1748_, v_b_1746_);
if (lean_obj_tag(v___x_1749_) == 0)
{
lean_object* v_a_1750_; 
v_a_1750_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1750_);
lean_dec_ref_known(v___x_1749_, 1);
return v_a_1750_;
}
else
{
lean_object* v_a_1751_; size_t v___x_1752_; size_t v___x_1753_; 
v_a_1751_ = lean_ctor_get(v___x_1749_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1749_, 1);
v___x_1752_ = ((size_t)1ULL);
v___x_1753_ = lean_usize_add(v_i_1745_, v___x_1752_);
v_i_1745_ = v___x_1753_;
v_b_1746_ = v_a_1751_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingletons_spec__1___boxed(lean_object* v_as_1755_, lean_object* v_sz_1756_, lean_object* v_i_1757_, lean_object* v_b_1758_){
_start:
{
size_t v_sz_boxed_1759_; size_t v_i_boxed_1760_; lean_object* v_res_1761_; 
v_sz_boxed_1759_ = lean_unbox_usize(v_sz_1756_);
lean_dec(v_sz_1756_);
v_i_boxed_1760_ = lean_unbox_usize(v_i_1757_);
lean_dec(v_i_1757_);
v_res_1761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingletons_spec__1(v_as_1755_, v_sz_boxed_1759_, v_i_boxed_1760_, v_b_1758_);
lean_dec_ref(v_as_1755_);
return v_res_1761_;
}
}
LEAN_EXPORT lean_object* l_eliminateSingletons(lean_object* v_p_1762_){
_start:
{
lean_object* v_equations_1763_; lean_object* v_buckets_1764_; lean_object* v_r_x3f_1765_; size_t v_sz_1766_; size_t v___x_1767_; lean_object* v___x_1768_; 
v_equations_1763_ = lean_ctor_get(v_p_1762_, 0);
v_buckets_1764_ = lean_ctor_get(v_equations_1763_, 1);
v_r_x3f_1765_ = lean_box(0);
v_sz_1766_ = lean_array_size(v_buckets_1764_);
v___x_1767_ = ((size_t)0ULL);
v___x_1768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00eliminateSingletons_spec__1(v_buckets_1764_, v_sz_1766_, v___x_1767_, v_r_x3f_1765_);
if (lean_obj_tag(v___x_1768_) == 0)
{
return v_p_1762_;
}
else
{
lean_object* v_val_1769_; lean_object* v_fst_1770_; lean_object* v_snd_1771_; lean_object* v___x_1772_; 
v_val_1769_ = lean_ctor_get(v___x_1768_, 0);
lean_inc(v_val_1769_);
lean_dec_ref_known(v___x_1768_, 1);
v_fst_1770_ = lean_ctor_get(v_val_1769_, 0);
lean_inc(v_fst_1770_);
v_snd_1771_ = lean_ctor_get(v_val_1769_, 1);
lean_inc(v_snd_1771_);
lean_dec(v_val_1769_);
v___x_1772_ = l_eliminateSingleton(v_p_1762_, v_fst_1770_, v_snd_1771_);
v_p_1762_ = v___x_1772_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_addAuxEquation___lam__0(lean_object* v___x_1774_, lean_object* v_x_1775_, lean_object* v_coeff_1776_){
_start:
{
lean_object* v___x_1777_; 
v___x_1777_ = l_Int_mod_x27(v_coeff_1776_, v___x_1774_);
return v___x_1777_;
}
}
LEAN_EXPORT lean_object* l_addAuxEquation___lam__0___boxed(lean_object* v___x_1778_, lean_object* v_x_1779_, lean_object* v_coeff_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_addAuxEquation___lam__0(v___x_1778_, v_x_1779_, v_coeff_1780_);
lean_dec(v_coeff_1780_);
lean_dec(v_x_1779_);
lean_dec(v___x_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_addAuxEquation___lam__1(lean_object* v___x_1782_, lean_object* v_x_1783_, lean_object* v_a_u1d62_1784_){
_start:
{
lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1785_ = l_Int_roundedDiv(v_a_u1d62_1784_, v___x_1782_);
v___x_1786_ = l_Int_mod_x27(v_a_u1d62_1784_, v___x_1782_);
v___x_1787_ = lean_int_add(v___x_1785_, v___x_1786_);
lean_dec(v___x_1786_);
lean_dec(v___x_1785_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_addAuxEquation___lam__1___boxed(lean_object* v___x_1788_, lean_object* v_x_1789_, lean_object* v_a_u1d62_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_addAuxEquation___lam__1(v___x_1788_, v_x_1789_, v_a_u1d62_1790_);
lean_dec(v_a_u1d62_1790_);
lean_dec(v_x_1789_);
lean_dec(v___x_1788_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__2(lean_object* v_acc_1792_, lean_object* v_a_1793_){
_start:
{
if (lean_obj_tag(v_a_1793_) == 0)
{
return v_acc_1792_;
}
else
{
lean_object* v_key_1794_; lean_object* v_value_1795_; lean_object* v_tail_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1807_; 
v_key_1794_ = lean_ctor_get(v_a_1793_, 0);
v_value_1795_ = lean_ctor_get(v_a_1793_, 1);
v_tail_1796_ = lean_ctor_get(v_a_1793_, 2);
v_isSharedCheck_1807_ = !lean_is_exclusive(v_a_1793_);
if (v_isSharedCheck_1807_ == 0)
{
v___x_1798_ = v_a_1793_;
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_tail_1796_);
lean_inc(v_value_1795_);
lean_inc(v_key_1794_);
lean_dec(v_a_1793_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1807_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; uint8_t v___x_1801_; 
v___x_1800_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_1801_ = lean_int_dec_eq(v_value_1795_, v___x_1800_);
if (v___x_1801_ == 0)
{
lean_object* v___x_1803_; 
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 2, v_acc_1792_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_key_1794_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_value_1795_);
lean_ctor_set(v_reuseFailAlloc_1805_, 2, v_acc_1792_);
v___x_1803_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
v_acc_1792_ = v___x_1803_;
v_a_1793_ = v_tail_1796_;
goto _start;
}
}
else
{
lean_del_object(v___x_1798_);
lean_dec(v_value_1795_);
lean_dec(v_key_1794_);
v_a_1793_ = v_tail_1796_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__3(size_t v_sz_1808_, size_t v_i_1809_, lean_object* v_bs_1810_){
_start:
{
uint8_t v___x_1811_; 
v___x_1811_ = lean_usize_dec_lt(v_i_1809_, v_sz_1808_);
if (v___x_1811_ == 0)
{
return v_bs_1810_;
}
else
{
lean_object* v_v_1812_; lean_object* v___x_1813_; lean_object* v_bs_x27_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v_v_1812_ = lean_array_uget(v_bs_1810_, v_i_1809_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v_bs_x27_1814_ = lean_array_uset(v_bs_1810_, v_i_1809_, v___x_1813_);
v___x_1815_ = lean_box(0);
v___x_1816_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__2(v___x_1815_, v_v_1812_);
v___x_1817_ = ((size_t)1ULL);
v___x_1818_ = lean_usize_add(v_i_1809_, v___x_1817_);
v___x_1819_ = lean_array_uset(v_bs_x27_1814_, v_i_1809_, v___x_1816_);
v_i_1809_ = v___x_1818_;
v_bs_1810_ = v___x_1819_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__3___boxed(lean_object* v_sz_1821_, lean_object* v_i_1822_, lean_object* v_bs_1823_){
_start:
{
size_t v_sz_boxed_1824_; size_t v_i_boxed_1825_; lean_object* v_res_1826_; 
v_sz_boxed_1824_ = lean_unbox_usize(v_sz_1821_);
lean_dec(v_sz_1821_);
v_i_boxed_1825_ = lean_unbox_usize(v_i_1822_);
lean_dec(v_i_1822_);
v_res_1826_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__3(v_sz_boxed_1824_, v_i_boxed_1825_, v_bs_1823_);
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2(lean_object* v_m_1827_){
_start:
{
lean_object* v_buckets_1828_; lean_object* v___x_1830_; uint8_t v_isShared_1831_; uint8_t v_isSharedCheck_1855_; 
v_buckets_1828_ = lean_ctor_get(v_m_1827_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v_m_1827_);
if (v_isSharedCheck_1855_ == 0)
{
lean_object* v_unused_1856_; 
v_unused_1856_ = lean_ctor_get(v_m_1827_, 0);
lean_dec(v_unused_1856_);
v___x_1830_ = v_m_1827_;
v_isShared_1831_ = v_isSharedCheck_1855_;
goto v_resetjp_1829_;
}
else
{
lean_inc(v_buckets_1828_);
lean_dec(v_m_1827_);
v___x_1830_ = lean_box(0);
v_isShared_1831_ = v_isSharedCheck_1855_;
goto v_resetjp_1829_;
}
v_resetjp_1829_:
{
size_t v_sz_1832_; size_t v___x_1833_; lean_object* v_newBuckets_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; uint8_t v___x_1837_; 
v_sz_1832_ = lean_array_size(v_buckets_1828_);
v___x_1833_ = ((size_t)0ULL);
v_newBuckets_1834_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2_spec__3(v_sz_1832_, v___x_1833_, v_buckets_1828_);
v___x_1835_ = lean_unsigned_to_nat(0u);
v___x_1836_ = lean_array_get_size(v_newBuckets_1834_);
v___x_1837_ = lean_nat_dec_lt(v___x_1835_, v___x_1836_);
if (v___x_1837_ == 0)
{
lean_object* v___x_1839_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_newBuckets_1834_);
lean_ctor_set(v___x_1830_, 0, v___x_1835_);
v___x_1839_ = v___x_1830_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1840_, 1, v_newBuckets_1834_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
else
{
uint8_t v___x_1841_; 
v___x_1841_ = lean_nat_dec_le(v___x_1836_, v___x_1836_);
if (v___x_1841_ == 0)
{
if (v___x_1837_ == 0)
{
lean_object* v___x_1843_; 
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_newBuckets_1834_);
lean_ctor_set(v___x_1830_, 0, v___x_1835_);
v___x_1843_ = v___x_1830_;
goto v_reusejp_1842_;
}
else
{
lean_object* v_reuseFailAlloc_1844_; 
v_reuseFailAlloc_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1844_, 0, v___x_1835_);
lean_ctor_set(v_reuseFailAlloc_1844_, 1, v_newBuckets_1834_);
v___x_1843_ = v_reuseFailAlloc_1844_;
goto v_reusejp_1842_;
}
v_reusejp_1842_:
{
return v___x_1843_;
}
}
else
{
size_t v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1848_; 
v___x_1845_ = lean_usize_of_nat(v___x_1836_);
v___x_1846_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(v_newBuckets_1834_, v___x_1833_, v___x_1845_, v___x_1835_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_newBuckets_1834_);
lean_ctor_set(v___x_1830_, 0, v___x_1846_);
v___x_1848_ = v___x_1830_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1849_; 
v_reuseFailAlloc_1849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1849_, 0, v___x_1846_);
lean_ctor_set(v_reuseFailAlloc_1849_, 1, v_newBuckets_1834_);
v___x_1848_ = v_reuseFailAlloc_1849_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
return v___x_1848_;
}
}
}
else
{
size_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1850_ = lean_usize_of_nat(v___x_1836_);
v___x_1851_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(v_newBuckets_1834_, v___x_1833_, v___x_1850_, v___x_1835_);
if (v_isShared_1831_ == 0)
{
lean_ctor_set(v___x_1830_, 1, v_newBuckets_1834_);
lean_ctor_set(v___x_1830_, 0, v___x_1851_);
v___x_1853_ = v___x_1830_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_newBuckets_1834_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__5(lean_object* v___y_1857_, lean_object* v_acc_1858_, lean_object* v_a_1859_){
_start:
{
if (lean_obj_tag(v_a_1859_) == 0)
{
return v_acc_1858_;
}
else
{
lean_object* v_key_1860_; lean_object* v_value_1861_; lean_object* v_tail_1862_; lean_object* v___x_1864_; uint8_t v_isShared_1865_; uint8_t v_isSharedCheck_1872_; 
v_key_1860_ = lean_ctor_get(v_a_1859_, 0);
v_value_1861_ = lean_ctor_get(v_a_1859_, 1);
v_tail_1862_ = lean_ctor_get(v_a_1859_, 2);
v_isSharedCheck_1872_ = !lean_is_exclusive(v_a_1859_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1864_ = v_a_1859_;
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
else
{
lean_inc(v_tail_1862_);
lean_inc(v_value_1861_);
lean_inc(v_key_1860_);
lean_dec(v_a_1859_);
v___x_1864_ = lean_box(0);
v_isShared_1865_ = v_isSharedCheck_1872_;
goto v_resetjp_1863_;
}
v_resetjp_1863_:
{
uint8_t v___x_1866_; 
v___x_1866_ = lean_nat_dec_eq(v_key_1860_, v___y_1857_);
if (v___x_1866_ == 0)
{
lean_object* v___x_1868_; 
if (v_isShared_1865_ == 0)
{
lean_ctor_set(v___x_1864_, 2, v_acc_1858_);
v___x_1868_ = v___x_1864_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_key_1860_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_value_1861_);
lean_ctor_set(v_reuseFailAlloc_1870_, 2, v_acc_1858_);
v___x_1868_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
v_acc_1858_ = v___x_1868_;
v_a_1859_ = v_tail_1862_;
goto _start;
}
}
else
{
lean_del_object(v___x_1864_);
lean_dec(v_value_1861_);
lean_dec(v_key_1860_);
v_a_1859_ = v_tail_1862_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__5___boxed(lean_object* v___y_1873_, lean_object* v_acc_1874_, lean_object* v_a_1875_){
_start:
{
lean_object* v_res_1876_; 
v_res_1876_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__5(v___y_1873_, v_acc_1874_, v_a_1875_);
lean_dec(v___y_1873_);
return v_res_1876_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__6(lean_object* v___y_1877_, size_t v_sz_1878_, size_t v_i_1879_, lean_object* v_bs_1880_){
_start:
{
uint8_t v___x_1881_; 
v___x_1881_ = lean_usize_dec_lt(v_i_1879_, v_sz_1878_);
if (v___x_1881_ == 0)
{
return v_bs_1880_;
}
else
{
lean_object* v_v_1882_; lean_object* v___x_1883_; lean_object* v_bs_x27_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; size_t v___x_1887_; size_t v___x_1888_; lean_object* v___x_1889_; 
v_v_1882_ = lean_array_uget(v_bs_1880_, v_i_1879_);
v___x_1883_ = lean_unsigned_to_nat(0u);
v_bs_x27_1884_ = lean_array_uset(v_bs_1880_, v_i_1879_, v___x_1883_);
v___x_1885_ = lean_box(0);
v___x_1886_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_filter_go___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__5(v___y_1877_, v___x_1885_, v_v_1882_);
v___x_1887_ = ((size_t)1ULL);
v___x_1888_ = lean_usize_add(v_i_1879_, v___x_1887_);
v___x_1889_ = lean_array_uset(v_bs_x27_1884_, v_i_1879_, v___x_1886_);
v_i_1879_ = v___x_1888_;
v_bs_1880_ = v___x_1889_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__6___boxed(lean_object* v___y_1891_, lean_object* v_sz_1892_, lean_object* v_i_1893_, lean_object* v_bs_1894_){
_start:
{
size_t v_sz_boxed_1895_; size_t v_i_boxed_1896_; lean_object* v_res_1897_; 
v_sz_boxed_1895_ = lean_unbox_usize(v_sz_1892_);
lean_dec(v_sz_1892_);
v_i_boxed_1896_ = lean_unbox_usize(v_i_1893_);
lean_dec(v_i_1893_);
v_res_1897_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__6(v___y_1891_, v_sz_boxed_1895_, v_i_boxed_1896_, v_bs_1894_);
lean_dec(v___y_1891_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3(lean_object* v___y_1898_, lean_object* v_m_1899_){
_start:
{
lean_object* v_buckets_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1927_; 
v_buckets_1900_ = lean_ctor_get(v_m_1899_, 1);
v_isSharedCheck_1927_ = !lean_is_exclusive(v_m_1899_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v_m_1899_, 0);
lean_dec(v_unused_1928_);
v___x_1902_ = v_m_1899_;
v_isShared_1903_ = v_isSharedCheck_1927_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_buckets_1900_);
lean_dec(v_m_1899_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1927_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
size_t v_sz_1904_; size_t v___x_1905_; lean_object* v_newBuckets_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; uint8_t v___x_1909_; 
v_sz_1904_ = lean_array_size(v_buckets_1900_);
v___x_1905_ = ((size_t)0ULL);
v_newBuckets_1906_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3_spec__6(v___y_1898_, v_sz_1904_, v___x_1905_, v_buckets_1900_);
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = lean_array_get_size(v_newBuckets_1906_);
v___x_1909_ = lean_nat_dec_lt(v___x_1907_, v___x_1908_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1911_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_newBuckets_1906_);
lean_ctor_set(v___x_1902_, 0, v___x_1907_);
v___x_1911_ = v___x_1902_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1912_, 1, v_newBuckets_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
else
{
uint8_t v___x_1913_; 
v___x_1913_ = lean_nat_dec_le(v___x_1908_, v___x_1908_);
if (v___x_1913_ == 0)
{
if (v___x_1909_ == 0)
{
lean_object* v___x_1915_; 
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_newBuckets_1906_);
lean_ctor_set(v___x_1902_, 0, v___x_1907_);
v___x_1915_ = v___x_1902_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v___x_1907_);
lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_newBuckets_1906_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
else
{
size_t v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1920_; 
v___x_1917_ = lean_usize_of_nat(v___x_1908_);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(v_newBuckets_1906_, v___x_1905_, v___x_1917_, v___x_1907_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_newBuckets_1906_);
lean_ctor_set(v___x_1902_, 0, v___x_1918_);
v___x_1920_ = v___x_1902_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_newBuckets_1906_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
else
{
size_t v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1925_; 
v___x_1922_ = lean_usize_of_nat(v___x_1908_);
v___x_1923_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_DHashMap_Internal_Raw_u2080_filter___at___00Equation_subst_spec__5_spec__9(v_newBuckets_1906_, v___x_1905_, v___x_1922_, v___x_1907_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 1, v_newBuckets_1906_);
lean_ctor_set(v___x_1902_, 0, v___x_1923_);
v___x_1925_ = v___x_1902_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1923_);
lean_ctor_set(v_reuseFailAlloc_1926_, 1, v_newBuckets_1906_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3___boxed(lean_object* v___y_1929_, lean_object* v_m_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3(v___y_1929_, v_m_1930_);
lean_dec(v___y_1929_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00addAuxEquation_spec__0(lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
if (lean_obj_tag(v_a_1932_) == 0)
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_a_1933_);
return v___x_1934_;
}
else
{
lean_object* v_snd_1935_; lean_object* v_value_1936_; lean_object* v_tail_1937_; lean_object* v_fst_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_2015_; 
v_snd_1935_ = lean_ctor_get(v_a_1933_, 1);
lean_inc(v_snd_1935_);
v_value_1936_ = lean_ctor_get(v_a_1932_, 1);
v_tail_1937_ = lean_ctor_get(v_a_1932_, 2);
v_fst_1938_ = lean_ctor_get(v_a_1933_, 0);
v_isSharedCheck_2015_ = !lean_is_exclusive(v_a_1933_);
if (v_isSharedCheck_2015_ == 0)
{
lean_object* v_unused_2016_; 
v_unused_2016_ = lean_ctor_get(v_a_1933_, 1);
lean_dec(v_unused_2016_);
v___x_1940_ = v_a_1933_;
v_isShared_1941_ = v_isSharedCheck_2015_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_fst_1938_);
lean_dec(v_a_1933_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_2015_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v_fst_1942_; lean_object* v_snd_1943_; lean_object* v___x_1945_; uint8_t v_isShared_1946_; uint8_t v_isSharedCheck_2014_; 
v_fst_1942_ = lean_ctor_get(v_snd_1935_, 0);
v_snd_1943_ = lean_ctor_get(v_snd_1935_, 1);
v_isSharedCheck_2014_ = !lean_is_exclusive(v_snd_1935_);
if (v_isSharedCheck_2014_ == 0)
{
v___x_1945_ = v_snd_1935_;
v_isShared_1946_ = v_isSharedCheck_2014_;
goto v_resetjp_1944_;
}
else
{
lean_inc(v_snd_1943_);
lean_inc(v_fst_1942_);
lean_dec(v_snd_1935_);
v___x_1945_ = lean_box(0);
v_isShared_1946_ = v_isSharedCheck_2014_;
goto v_resetjp_1944_;
}
v_resetjp_1944_:
{
lean_object* v___x_1947_; 
v___x_1947_ = l_Equation_findAbsMinimumCoeff_x3f(v_value_1936_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v___x_1949_; 
if (v_isShared_1946_ == 0)
{
v___x_1949_ = v___x_1945_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1954_; 
v_reuseFailAlloc_1954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1954_, 0, v_fst_1942_);
lean_ctor_set(v_reuseFailAlloc_1954_, 1, v_snd_1943_);
v___x_1949_ = v_reuseFailAlloc_1954_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
lean_object* v___x_1951_; 
if (v_isShared_1941_ == 0)
{
lean_ctor_set(v___x_1940_, 1, v___x_1949_);
v___x_1951_ = v___x_1940_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_fst_1938_);
lean_ctor_set(v_reuseFailAlloc_1953_, 1, v___x_1949_);
v___x_1951_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
v_a_1932_ = v_tail_1937_;
v_a_1933_ = v___x_1951_;
goto _start;
}
}
}
else
{
lean_object* v_val_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_2013_; 
lean_del_object(v___x_1940_);
v_val_1955_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_1957_ = v___x_1947_;
v_isShared_1958_ = v_isSharedCheck_2013_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_val_1955_);
lean_dec(v___x_1947_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_2013_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
if (lean_obj_tag(v_snd_1943_) == 0)
{
lean_object* v_fst_1959_; lean_object* v_snd_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1976_; 
lean_dec(v_fst_1942_);
lean_dec(v_fst_1938_);
v_fst_1959_ = lean_ctor_get(v_val_1955_, 0);
v_snd_1960_ = lean_ctor_get(v_val_1955_, 1);
v_isSharedCheck_1976_ = !lean_is_exclusive(v_val_1955_);
if (v_isSharedCheck_1976_ == 0)
{
v___x_1962_ = v_val_1955_;
v_isShared_1963_ = v_isSharedCheck_1976_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_snd_1960_);
lean_inc(v_fst_1959_);
lean_dec(v_val_1955_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1976_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
lean_inc(v_value_1936_);
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_value_1936_);
v___x_1965_ = v___x_1957_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1975_; 
v_reuseFailAlloc_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1975_, 0, v_value_1936_);
v___x_1965_ = v_reuseFailAlloc_1975_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
lean_object* v___x_1966_; lean_object* v___x_1967_; lean_object* v___x_1969_; 
v___x_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1966_, 0, v_fst_1959_);
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_snd_1960_);
if (v_isShared_1963_ == 0)
{
lean_ctor_set(v___x_1962_, 1, v___x_1967_);
lean_ctor_set(v___x_1962_, 0, v___x_1966_);
v___x_1969_ = v___x_1962_;
goto v_reusejp_1968_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1966_);
lean_ctor_set(v_reuseFailAlloc_1974_, 1, v___x_1967_);
v___x_1969_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1968_;
}
v_reusejp_1968_:
{
lean_object* v___x_1971_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1969_);
lean_ctor_set(v___x_1945_, 0, v___x_1965_);
v___x_1971_ = v___x_1945_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1973_; 
v_reuseFailAlloc_1973_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1973_, 0, v___x_1965_);
lean_ctor_set(v_reuseFailAlloc_1973_, 1, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1973_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
v_a_1932_ = v_tail_1937_;
v_a_1933_ = v___x_1971_;
goto _start;
}
}
}
}
}
else
{
lean_object* v_fst_1977_; lean_object* v_snd_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2012_; 
v_fst_1977_ = lean_ctor_get(v_val_1955_, 0);
v_snd_1978_ = lean_ctor_get(v_val_1955_, 1);
v_isSharedCheck_2012_ = !lean_is_exclusive(v_val_1955_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_1980_ = v_val_1955_;
v_isShared_1981_ = v_isSharedCheck_2012_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_snd_1978_);
lean_inc(v_fst_1977_);
lean_dec(v_val_1955_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2012_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
lean_object* v_val_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; uint8_t v___x_1985_; 
v_val_1982_ = lean_ctor_get(v_snd_1943_, 0);
v___x_1983_ = lean_nat_abs(v_snd_1978_);
v___x_1984_ = lean_nat_abs(v_val_1982_);
v___x_1985_ = lean_nat_dec_lt(v___x_1983_, v___x_1984_);
lean_dec(v___x_1984_);
lean_dec(v___x_1983_);
if (v___x_1985_ == 0)
{
lean_object* v___x_1987_; 
lean_dec(v_snd_1978_);
lean_dec(v_fst_1977_);
lean_del_object(v___x_1957_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v_snd_1943_);
lean_ctor_set(v___x_1980_, 0, v_fst_1942_);
v___x_1987_ = v___x_1980_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_fst_1942_);
lean_ctor_set(v_reuseFailAlloc_1992_, 1, v_snd_1943_);
v___x_1987_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
lean_object* v___x_1989_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_1987_);
lean_ctor_set(v___x_1945_, 0, v_fst_1938_);
v___x_1989_ = v___x_1945_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_fst_1938_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
v_a_1932_ = v_tail_1937_;
v_a_1933_ = v___x_1989_;
goto _start;
}
}
}
else
{
lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2010_; 
lean_dec(v_fst_1942_);
lean_dec(v_fst_1938_);
v_isSharedCheck_2010_ = !lean_is_exclusive(v_snd_1943_);
if (v_isSharedCheck_2010_ == 0)
{
lean_object* v_unused_2011_; 
v_unused_2011_ = lean_ctor_get(v_snd_1943_, 0);
lean_dec(v_unused_2011_);
v___x_1994_ = v_snd_1943_;
v_isShared_1995_ = v_isSharedCheck_2010_;
goto v_resetjp_1993_;
}
else
{
lean_dec(v_snd_1943_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2010_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v___x_1997_; 
lean_inc(v_value_1936_);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_value_1936_);
v___x_1997_ = v___x_1994_;
goto v_reusejp_1996_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_value_1936_);
v___x_1997_ = v_reuseFailAlloc_2009_;
goto v_reusejp_1996_;
}
v_reusejp_1996_:
{
lean_object* v___x_1999_; 
if (v_isShared_1958_ == 0)
{
lean_ctor_set(v___x_1957_, 0, v_fst_1977_);
v___x_1999_ = v___x_1957_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v_fst_1977_);
v___x_1999_ = v_reuseFailAlloc_2008_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
lean_object* v___x_2000_; lean_object* v___x_2002_; 
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v_snd_1978_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 1, v___x_2000_);
lean_ctor_set(v___x_1980_, 0, v___x_1999_);
v___x_2002_ = v___x_1980_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v___x_1999_);
lean_ctor_set(v_reuseFailAlloc_2007_, 1, v___x_2000_);
v___x_2002_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
lean_object* v___x_2004_; 
if (v_isShared_1946_ == 0)
{
lean_ctor_set(v___x_1945_, 1, v___x_2002_);
lean_ctor_set(v___x_1945_, 0, v___x_1997_);
v___x_2004_ = v___x_1945_;
goto v_reusejp_2003_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1997_);
lean_ctor_set(v_reuseFailAlloc_2006_, 1, v___x_2002_);
v___x_2004_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2003_;
}
v_reusejp_2003_:
{
v_a_1932_ = v_tail_1937_;
v_a_1933_ = v___x_2004_;
goto _start;
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
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00addAuxEquation_spec__0___boxed(lean_object* v_a_2017_, lean_object* v_a_2018_){
_start:
{
lean_object* v_res_2019_; 
v_res_2019_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00addAuxEquation_spec__0(v_a_2017_, v_a_2018_);
lean_dec(v_a_2017_);
return v_res_2019_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00addAuxEquation_spec__1(lean_object* v_as_2020_, size_t v_sz_2021_, size_t v_i_2022_, lean_object* v_b_2023_){
_start:
{
uint8_t v___x_2024_; 
v___x_2024_ = lean_usize_dec_lt(v_i_2022_, v_sz_2021_);
if (v___x_2024_ == 0)
{
return v_b_2023_;
}
else
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_array_uget_borrowed(v_as_2020_, v_i_2022_);
v___x_2026_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00addAuxEquation_spec__0(v_a_2025_, v_b_2023_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
return v_a_2027_;
}
else
{
lean_object* v_a_2028_; size_t v___x_2029_; size_t v___x_2030_; 
v_a_2028_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2029_ = ((size_t)1ULL);
v___x_2030_ = lean_usize_add(v_i_2022_, v___x_2029_);
v_i_2022_ = v___x_2030_;
v_b_2023_ = v_a_2028_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00addAuxEquation_spec__1___boxed(lean_object* v_as_2032_, lean_object* v_sz_2033_, lean_object* v_i_2034_, lean_object* v_b_2035_){
_start:
{
size_t v_sz_boxed_2036_; size_t v_i_boxed_2037_; lean_object* v_res_2038_; 
v_sz_boxed_2036_ = lean_unbox_usize(v_sz_2033_);
lean_dec(v_sz_2033_);
v_i_boxed_2037_ = lean_unbox_usize(v_i_2034_);
lean_dec(v_i_2034_);
v_res_2038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00addAuxEquation_spec__1(v_as_2032_, v_sz_boxed_2036_, v_i_boxed_2037_, v_b_2035_);
lean_dec_ref(v_as_2032_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l_addAuxEquation(lean_object* v_p_2044_){
_start:
{
lean_object* v_equations_2045_; lean_object* v_solvedEquations_2046_; lean_object* v_nEquations_2047_; lean_object* v_nVars_2048_; lean_object* v___x_2050_; uint8_t v_isShared_2051_; uint8_t v_isSharedCheck_2125_; 
v_equations_2045_ = lean_ctor_get(v_p_2044_, 0);
v_solvedEquations_2046_ = lean_ctor_get(v_p_2044_, 1);
v_nEquations_2047_ = lean_ctor_get(v_p_2044_, 2);
v_nVars_2048_ = lean_ctor_get(v_p_2044_, 3);
v_isSharedCheck_2125_ = !lean_is_exclusive(v_p_2044_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2050_ = v_p_2044_;
v_isShared_2051_ = v_isSharedCheck_2125_;
goto v_resetjp_2049_;
}
else
{
lean_inc(v_nVars_2048_);
lean_inc(v_nEquations_2047_);
lean_inc(v_solvedEquations_2046_);
lean_inc(v_equations_2045_);
lean_dec(v_p_2044_);
v___x_2050_ = lean_box(0);
v_isShared_2051_ = v_isSharedCheck_2125_;
goto v_resetjp_2049_;
}
v_resetjp_2049_:
{
lean_object* v___y_2053_; lean_object* v_E_2054_; lean_object* v_a_u2096_2055_; lean_object* v___y_2095_; lean_object* v___y_2096_; lean_object* v___y_2097_; lean_object* v_buckets_2102_; lean_object* v___x_2103_; size_t v_sz_2104_; size_t v___x_2105_; lean_object* v___x_2106_; lean_object* v_snd_2107_; lean_object* v_fst_2108_; lean_object* v_fst_2109_; lean_object* v_snd_2110_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2118_; 
v_buckets_2102_ = lean_ctor_get(v_equations_2045_, 1);
v___x_2103_ = ((lean_object*)(l_addAuxEquation___closed__1));
v_sz_2104_ = lean_array_size(v_buckets_2102_);
v___x_2105_ = ((size_t)0ULL);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00addAuxEquation_spec__1(v_buckets_2102_, v_sz_2104_, v___x_2105_, v___x_2103_);
v_snd_2107_ = lean_ctor_get(v___x_2106_, 1);
lean_inc(v_snd_2107_);
v_fst_2108_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_fst_2108_);
lean_dec_ref(v___x_2106_);
v_fst_2109_ = lean_ctor_get(v_snd_2107_, 0);
lean_inc(v_fst_2109_);
v_snd_2110_ = lean_ctor_get(v_snd_2107_, 1);
lean_inc(v_snd_2110_);
lean_dec(v_snd_2107_);
if (lean_obj_tag(v_fst_2108_) == 0)
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = lean_obj_once(&l_Equation_normalize___closed__3, &l_Equation_normalize___closed__3_once, _init_l_Equation_normalize___closed__3);
v___x_2123_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Std_HashMap_modify_x21___at___00eliminateSingleton_spec__0_spec__0_spec__1_spec__5(v___x_2122_);
v___y_2118_ = v___x_2123_;
goto v___jp_2117_;
}
else
{
lean_object* v_val_2124_; 
v_val_2124_ = lean_ctor_get(v_fst_2108_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v_fst_2108_, 1);
v___y_2118_ = v_val_2124_;
goto v___jp_2117_;
}
v___jp_2052_:
{
lean_object* v_id_2056_; lean_object* v_coeffs_2057_; lean_object* v_const_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2093_; 
v_id_2056_ = lean_ctor_get(v_E_2054_, 0);
v_coeffs_2057_ = lean_ctor_get(v_E_2054_, 1);
v_const_2058_ = lean_ctor_get(v_E_2054_, 2);
v_isSharedCheck_2093_ = !lean_is_exclusive(v_E_2054_);
if (v_isSharedCheck_2093_ == 0)
{
v___x_2060_ = v_E_2054_;
v_isShared_2061_ = v_isSharedCheck_2093_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_const_2058_);
lean_inc(v_coeffs_2057_);
lean_inc(v_id_2056_);
lean_dec(v_E_2054_);
v___x_2060_ = lean_box(0);
v_isShared_2061_ = v_isSharedCheck_2093_;
goto v_resetjp_2059_;
}
v_resetjp_2059_:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___f_2065_; lean_object* v___f_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2062_ = lean_unsigned_to_nat(1u);
v___x_2063_ = lean_obj_once(&l_Int_roundedDiv___closed__2, &l_Int_roundedDiv___closed__2_once, _init_l_Int_roundedDiv___closed__2);
v___x_2064_ = lean_int_add(v_a_u2096_2055_, v___x_2063_);
lean_inc_n(v___x_2064_, 2);
v___f_2065_ = lean_alloc_closure((void*)(l_addAuxEquation___lam__0___boxed), 3, 1);
lean_closure_set(v___f_2065_, 0, v___x_2064_);
v___f_2066_ = lean_alloc_closure((void*)(l_addAuxEquation___lam__1___boxed), 3, 1);
lean_closure_set(v___f_2066_, 0, v___x_2064_);
lean_inc_ref(v_coeffs_2057_);
v___x_2067_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v___f_2065_, v_coeffs_2057_);
v___x_2068_ = lean_int_neg(v___x_2064_);
lean_inc_n(v_nVars_2048_, 2);
v___x_2069_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v___x_2067_, v_nVars_2048_, v___x_2068_);
v___x_2070_ = l_Int_mod_x27(v_const_2058_, v___x_2064_);
v___x_2071_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__3(v___y_2053_, v_coeffs_2057_);
v___x_2072_ = l_Std_DHashMap_Internal_Raw_u2080_map___at___00Std_HashMap_fastMapVals___at___00Equation_preprocess_x3f_spec__0_spec__0___redArg(v___f_2066_, v___x_2071_);
v___x_2073_ = lean_int_neg(v_a_u2096_2055_);
lean_dec(v_a_u2096_2055_);
v___x_2074_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v___x_2072_, v_nVars_2048_, v___x_2073_);
v___x_2075_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2(v___x_2074_);
v___x_2076_ = l_Int_roundedDiv(v_const_2058_, v___x_2064_);
lean_dec(v___x_2064_);
lean_dec(v_const_2058_);
v___x_2077_ = lean_int_add(v___x_2076_, v___x_2070_);
lean_dec(v___x_2076_);
if (v_isShared_2061_ == 0)
{
lean_ctor_set(v___x_2060_, 2, v___x_2077_);
lean_ctor_set(v___x_2060_, 1, v___x_2075_);
v___x_2079_ = v___x_2060_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2092_; 
v_reuseFailAlloc_2092_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_id_2056_);
lean_ctor_set(v_reuseFailAlloc_2092_, 1, v___x_2075_);
lean_ctor_set(v_reuseFailAlloc_2092_, 2, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2092_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
lean_object* v___x_2080_; lean_object* v_id_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2089_; 
v___x_2080_ = l_Equation_normalize(v___x_2079_);
v_id_2081_ = lean_ctor_get(v___x_2080_, 0);
lean_inc(v_id_2081_);
v___x_2082_ = l_Std_DHashMap_Internal_Raw_u2080_filter___at___00addAuxEquation_spec__2(v___x_2069_);
lean_inc_n(v_nEquations_2047_, 2);
v___x_2083_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2083_, 0, v_nEquations_2047_);
lean_ctor_set(v___x_2083_, 1, v___x_2082_);
lean_ctor_set(v___x_2083_, 2, v___x_2070_);
v___x_2084_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_equations_2045_, v_id_2081_, v___x_2080_);
lean_inc_ref(v___x_2083_);
v___x_2085_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v___x_2084_, v_nEquations_2047_, v___x_2083_);
v___x_2086_ = lean_nat_add(v_nEquations_2047_, v___x_2062_);
lean_dec(v_nEquations_2047_);
v___x_2087_ = lean_nat_add(v_nVars_2048_, v___x_2062_);
lean_dec(v_nVars_2048_);
if (v_isShared_2051_ == 0)
{
lean_ctor_set(v___x_2050_, 3, v___x_2087_);
lean_ctor_set(v___x_2050_, 2, v___x_2086_);
lean_ctor_set(v___x_2050_, 0, v___x_2085_);
v___x_2089_ = v___x_2050_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2085_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_solvedEquations_2046_);
lean_ctor_set(v_reuseFailAlloc_2091_, 2, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2091_, 3, v___x_2087_);
v___x_2089_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_eliminateSingleton(v___x_2089_, v___x_2083_, v___y_2053_);
return v___x_2090_;
}
}
}
}
v___jp_2094_:
{
lean_object* v___x_2098_; uint8_t v___x_2099_; 
v___x_2098_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_2099_ = lean_int_dec_lt(v___y_2097_, v___x_2098_);
if (v___x_2099_ == 0)
{
v___y_2053_ = v___y_2096_;
v_E_2054_ = v___y_2095_;
v_a_u2096_2055_ = v___y_2097_;
goto v___jp_2052_;
}
else
{
lean_object* v___x_2100_; lean_object* v___x_2101_; 
v___x_2100_ = lean_int_neg(v___y_2097_);
lean_dec(v___y_2097_);
v___x_2101_ = l_Equation_invert(v___y_2095_);
v___y_2053_ = v___y_2096_;
v_E_2054_ = v___x_2101_;
v_a_u2096_2055_ = v___x_2100_;
goto v___jp_2052_;
}
}
v___jp_2111_:
{
if (lean_obj_tag(v_snd_2110_) == 0)
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = lean_obj_once(&l_Equation_normalize___closed__3, &l_Equation_normalize___closed__3_once, _init_l_Equation_normalize___closed__3);
v___x_2115_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0_spec__1(v___x_2114_);
v___y_2095_ = v___y_2112_;
v___y_2096_ = v___y_2113_;
v___y_2097_ = v___x_2115_;
goto v___jp_2094_;
}
else
{
lean_object* v_val_2116_; 
v_val_2116_ = lean_ctor_get(v_snd_2110_, 0);
lean_inc(v_val_2116_);
lean_dec_ref_known(v_snd_2110_, 1);
v___y_2095_ = v___y_2112_;
v___y_2096_ = v___y_2113_;
v___y_2097_ = v_val_2116_;
goto v___jp_2094_;
}
}
v___jp_2117_:
{
if (lean_obj_tag(v_fst_2109_) == 0)
{
lean_object* v___x_2119_; lean_object* v___x_2120_; 
v___x_2119_ = lean_obj_once(&l_Equation_normalize___closed__3, &l_Equation_normalize___closed__3_once, _init_l_Equation_normalize___closed__3);
v___x_2120_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_2119_);
v___y_2112_ = v___y_2118_;
v___y_2113_ = v___x_2120_;
goto v___jp_2111_;
}
else
{
lean_object* v_val_2121_; 
v_val_2121_ = lean_ctor_get(v_fst_2109_, 0);
lean_inc(v_val_2121_);
lean_dec_ref_known(v_fst_2109_, 1);
v___y_2112_ = v___y_2118_;
v___y_2113_ = v_val_2121_;
goto v___jp_2111_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Solution_ctorIdx(lean_object* v_x_2126_){
_start:
{
if (lean_obj_tag(v_x_2126_) == 0)
{
lean_object* v___x_2127_; 
v___x_2127_ = lean_unsigned_to_nat(0u);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; 
v___x_2128_ = lean_unsigned_to_nat(1u);
return v___x_2128_;
}
}
}
LEAN_EXPORT lean_object* l_Solution_ctorIdx___boxed(lean_object* v_x_2129_){
_start:
{
lean_object* v_res_2130_; 
v_res_2130_ = l_Solution_ctorIdx(v_x_2129_);
lean_dec(v_x_2129_);
return v_res_2130_;
}
}
LEAN_EXPORT lean_object* l_Solution_ctorElim___redArg(lean_object* v_t_2131_, lean_object* v_k_2132_){
_start:
{
if (lean_obj_tag(v_t_2131_) == 0)
{
return v_k_2132_;
}
else
{
lean_object* v_assignment_2133_; lean_object* v___x_2134_; 
v_assignment_2133_ = lean_ctor_get(v_t_2131_, 0);
lean_inc_ref(v_assignment_2133_);
lean_dec_ref_known(v_t_2131_, 1);
v___x_2134_ = lean_apply_1(v_k_2132_, v_assignment_2133_);
return v___x_2134_;
}
}
}
LEAN_EXPORT lean_object* l_Solution_ctorElim(lean_object* v_motive_2135_, lean_object* v_ctorIdx_2136_, lean_object* v_t_2137_, lean_object* v_h_2138_, lean_object* v_k_2139_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Solution_ctorElim___redArg(v_t_2137_, v_k_2139_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Solution_ctorElim___boxed(lean_object* v_motive_2141_, lean_object* v_ctorIdx_2142_, lean_object* v_t_2143_, lean_object* v_h_2144_, lean_object* v_k_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l_Solution_ctorElim(v_motive_2141_, v_ctorIdx_2142_, v_t_2143_, v_h_2144_, v_k_2145_);
lean_dec(v_ctorIdx_2142_);
return v_res_2146_;
}
}
LEAN_EXPORT lean_object* l_Solution_unsat_elim___redArg(lean_object* v_t_2147_, lean_object* v_unsat_2148_){
_start:
{
lean_object* v___x_2149_; 
v___x_2149_ = l_Solution_ctorElim___redArg(v_t_2147_, v_unsat_2148_);
return v___x_2149_;
}
}
LEAN_EXPORT lean_object* l_Solution_unsat_elim(lean_object* v_motive_2150_, lean_object* v_t_2151_, lean_object* v_h_2152_, lean_object* v_unsat_2153_){
_start:
{
lean_object* v___x_2154_; 
v___x_2154_ = l_Solution_ctorElim___redArg(v_t_2151_, v_unsat_2153_);
return v___x_2154_;
}
}
LEAN_EXPORT lean_object* l_Solution_sat_elim___redArg(lean_object* v_t_2155_, lean_object* v_sat_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = l_Solution_ctorElim___redArg(v_t_2155_, v_sat_2156_);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l_Solution_sat_elim(lean_object* v_motive_2158_, lean_object* v_t_2159_, lean_object* v_h_2160_, lean_object* v_sat_2161_){
_start:
{
lean_object* v___x_2162_; 
v___x_2162_ = l_Solution_ctorElim___redArg(v_t_2159_, v_sat_2161_);
return v___x_2162_;
}
}
static lean_object* _init_l_instInhabitedSolution_default(void){
_start:
{
lean_object* v___x_2163_; 
v___x_2163_ = lean_box(0);
return v___x_2163_;
}
}
static lean_object* _init_l_instInhabitedSolution(void){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_box(0);
return v___x_2164_;
}
}
static lean_object* _init_l_readSolution_x3f_readSolution___closed__0(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2165_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_2166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_readSolution_x3f_readSolution(lean_object* v_p_2167_, lean_object* v_varIdx_2168_, lean_object* v_assignment_2169_){
_start:
{
lean_object* v_solvedEquations_2170_; lean_object* v___x_2171_; 
v_solvedEquations_2170_ = lean_ctor_get(v_p_2167_, 1);
v___x_2171_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Equation_subst_spec__3___redArg(v_solvedEquations_2170_, v_varIdx_2168_);
if (lean_obj_tag(v___x_2171_) == 0)
{
lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2172_ = lean_obj_once(&l_readSolution_x3f_readSolution___closed__0, &l_readSolution_x3f_readSolution___closed__0_once, _init_l_readSolution_x3f_readSolution___closed__0);
v___x_2173_ = lean_array_set(v_assignment_2169_, v_varIdx_2168_, v___x_2172_);
return v___x_2173_;
}
else
{
lean_object* v_val_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2198_; 
v_val_2174_ = lean_ctor_get(v___x_2171_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2171_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2176_ = v___x_2171_;
v_isShared_2177_ = v_isSharedCheck_2198_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_val_2174_);
lean_dec(v___x_2171_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2198_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v_coeffs_2178_; lean_object* v_const_2179_; lean_object* v_buckets_2180_; lean_object* v___x_2182_; uint8_t v_isShared_2183_; uint8_t v_isSharedCheck_2196_; 
v_coeffs_2178_ = lean_ctor_get(v_val_2174_, 1);
lean_inc_ref(v_coeffs_2178_);
v_const_2179_ = lean_ctor_get(v_val_2174_, 2);
lean_inc(v_const_2179_);
lean_dec(v_val_2174_);
v_buckets_2180_ = lean_ctor_get(v_coeffs_2178_, 1);
v_isSharedCheck_2196_ = !lean_is_exclusive(v_coeffs_2178_);
if (v_isSharedCheck_2196_ == 0)
{
lean_object* v_unused_2197_; 
v_unused_2197_ = lean_ctor_get(v_coeffs_2178_, 0);
lean_dec(v_unused_2197_);
v___x_2182_ = v_coeffs_2178_;
v_isShared_2183_ = v_isSharedCheck_2196_;
goto v_resetjp_2181_;
}
else
{
lean_inc(v_buckets_2180_);
lean_dec(v_coeffs_2178_);
v___x_2182_ = lean_box(0);
v_isShared_2183_ = v_isSharedCheck_2196_;
goto v_resetjp_2181_;
}
v_resetjp_2181_:
{
lean_object* v___x_2185_; 
if (v_isShared_2183_ == 0)
{
lean_ctor_set(v___x_2182_, 1, v_const_2179_);
lean_ctor_set(v___x_2182_, 0, v_assignment_2169_);
v___x_2185_ = v___x_2182_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_assignment_2169_);
lean_ctor_set(v_reuseFailAlloc_2195_, 1, v_const_2179_);
v___x_2185_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
size_t v_sz_2186_; size_t v___x_2187_; lean_object* v___x_2188_; lean_object* v_fst_2189_; lean_object* v_snd_2190_; lean_object* v___x_2192_; 
v_sz_2186_ = lean_array_size(v_buckets_2180_);
v___x_2187_ = ((size_t)0ULL);
v___x_2188_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_readSolution_spec__1(v_p_2167_, v_buckets_2180_, v_sz_2186_, v___x_2187_, v___x_2185_);
lean_dec_ref(v_buckets_2180_);
v_fst_2189_ = lean_ctor_get(v___x_2188_, 0);
lean_inc(v_fst_2189_);
v_snd_2190_ = lean_ctor_get(v___x_2188_, 1);
lean_inc(v_snd_2190_);
lean_dec_ref(v___x_2188_);
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 0, v_snd_2190_);
v___x_2192_ = v___x_2176_;
goto v_reusejp_2191_;
}
else
{
lean_object* v_reuseFailAlloc_2194_; 
v_reuseFailAlloc_2194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2194_, 0, v_snd_2190_);
v___x_2192_ = v_reuseFailAlloc_2194_;
goto v_reusejp_2191_;
}
v_reusejp_2191_:
{
lean_object* v___x_2193_; 
v___x_2193_ = lean_array_set(v_fst_2189_, v_varIdx_2168_, v___x_2192_);
return v___x_2193_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_readSolution_spec__0(lean_object* v_p_2199_, lean_object* v_a_2200_, lean_object* v_a_2201_){
_start:
{
if (lean_obj_tag(v_a_2200_) == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_a_2201_);
return v___x_2202_;
}
else
{
lean_object* v_key_2203_; lean_object* v_value_2204_; lean_object* v_tail_2205_; lean_object* v_fst_2206_; lean_object* v_snd_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2229_; 
v_key_2203_ = lean_ctor_get(v_a_2200_, 0);
v_value_2204_ = lean_ctor_get(v_a_2200_, 1);
v_tail_2205_ = lean_ctor_get(v_a_2200_, 2);
v_fst_2206_ = lean_ctor_get(v_a_2201_, 0);
v_snd_2207_ = lean_ctor_get(v_a_2201_, 1);
v_isSharedCheck_2229_ = !lean_is_exclusive(v_a_2201_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2209_ = v_a_2201_;
v_isShared_2210_ = v_isSharedCheck_2229_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_snd_2207_);
lean_inc(v_fst_2206_);
lean_dec(v_a_2201_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2229_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___x_2220_; lean_object* v_assignment_2222_; lean_object* v___x_2227_; 
v___x_2220_ = lean_box(0);
v___x_2227_ = lean_array_get_borrowed(v___x_2220_, v_fst_2206_, v_key_2203_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v___x_2228_; 
v___x_2228_ = l_readSolution_x3f_readSolution(v_p_2199_, v_key_2203_, v_fst_2206_);
v_assignment_2222_ = v___x_2228_;
goto v___jp_2221_;
}
else
{
v_assignment_2222_ = v_fst_2206_;
goto v___jp_2221_;
}
v___jp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2217_; 
v___x_2214_ = lean_int_mul(v_value_2204_, v___y_2213_);
lean_dec(v___y_2213_);
v___x_2215_ = lean_int_add(v_snd_2207_, v___x_2214_);
lean_dec(v___x_2214_);
lean_dec(v_snd_2207_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 1, v___x_2215_);
lean_ctor_set(v___x_2209_, 0, v___y_2212_);
v___x_2217_ = v___x_2209_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v___y_2212_);
lean_ctor_set(v_reuseFailAlloc_2219_, 1, v___x_2215_);
v___x_2217_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
v_a_2200_ = v_tail_2205_;
v_a_2201_ = v___x_2217_;
goto _start;
}
}
v___jp_2221_:
{
lean_object* v___x_2223_; 
v___x_2223_ = lean_array_get_borrowed(v___x_2220_, v_assignment_2222_, v_key_2203_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2224_ = lean_obj_once(&l_Equation_normalize___closed__3, &l_Equation_normalize___closed__3_once, _init_l_Equation_normalize___closed__3);
v___x_2225_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0_spec__1(v___x_2224_);
v___y_2212_ = v_assignment_2222_;
v___y_2213_ = v___x_2225_;
goto v___jp_2211_;
}
else
{
lean_object* v_val_2226_; 
v_val_2226_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_val_2226_);
v___y_2212_ = v_assignment_2222_;
v___y_2213_ = v_val_2226_;
goto v___jp_2211_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_readSolution_spec__1(lean_object* v_p_2230_, lean_object* v_as_2231_, size_t v_sz_2232_, size_t v_i_2233_, lean_object* v_b_2234_){
_start:
{
uint8_t v___x_2235_; 
v___x_2235_ = lean_usize_dec_lt(v_i_2233_, v_sz_2232_);
if (v___x_2235_ == 0)
{
return v_b_2234_;
}
else
{
lean_object* v_a_2236_; lean_object* v___x_2237_; 
v_a_2236_ = lean_array_uget_borrowed(v_as_2231_, v_i_2233_);
v___x_2237_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_readSolution_spec__0(v_p_2230_, v_a_2236_, v_b_2234_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
return v_a_2238_;
}
else
{
lean_object* v_a_2239_; size_t v___x_2240_; size_t v___x_2241_; 
v_a_2239_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2240_ = ((size_t)1ULL);
v___x_2241_ = lean_usize_add(v_i_2233_, v___x_2240_);
v_i_2233_ = v___x_2241_;
v_b_2234_ = v_a_2239_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_readSolution_spec__1___boxed(lean_object* v_p_2243_, lean_object* v_as_2244_, lean_object* v_sz_2245_, lean_object* v_i_2246_, lean_object* v_b_2247_){
_start:
{
size_t v_sz_boxed_2248_; size_t v_i_boxed_2249_; lean_object* v_res_2250_; 
v_sz_boxed_2248_ = lean_unbox_usize(v_sz_2245_);
lean_dec(v_sz_2245_);
v_i_boxed_2249_ = lean_unbox_usize(v_i_2246_);
lean_dec(v_i_2246_);
v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_readSolution_spec__1(v_p_2243_, v_as_2244_, v_sz_boxed_2248_, v_i_boxed_2249_, v_b_2247_);
lean_dec_ref(v_as_2244_);
lean_dec_ref(v_p_2243_);
return v_res_2250_;
}
}
LEAN_EXPORT lean_object* l_readSolution_x3f_readSolution___boxed(lean_object* v_p_2251_, lean_object* v_varIdx_2252_, lean_object* v_assignment_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l_readSolution_x3f_readSolution(v_p_2251_, v_varIdx_2252_, v_assignment_2253_);
lean_dec(v_varIdx_2252_);
lean_dec_ref(v_p_2251_);
return v_res_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_readSolution_spec__0___boxed(lean_object* v_p_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_readSolution_spec__0(v_p_2255_, v_a_2256_, v_a_2257_);
lean_dec(v_a_2256_);
lean_dec_ref(v_p_2255_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2(lean_object* v_a_2270_, lean_object* v_a_2271_){
_start:
{
if (lean_obj_tag(v_a_2270_) == 0)
{
lean_object* v___x_2272_; 
v___x_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2272_, 0, v_a_2271_);
return v___x_2272_;
}
else
{
lean_object* v_value_2273_; lean_object* v_tail_2274_; lean_object* v_const_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; 
lean_dec_ref(v_a_2271_);
v_value_2273_ = lean_ctor_get(v_a_2270_, 1);
v_tail_2274_ = lean_ctor_get(v_a_2270_, 2);
v_const_2275_ = lean_ctor_get(v_value_2273_, 2);
v___x_2276_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_2277_ = lean_int_dec_eq(v_const_2275_, v___x_2276_);
if (v___x_2277_ == 0)
{
lean_object* v___x_2278_; 
v___x_2278_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__2));
return v___x_2278_;
}
else
{
lean_object* v___x_2279_; 
v___x_2279_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3));
v_a_2270_ = v_tail_2274_;
v_a_2271_ = v___x_2279_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___boxed(lean_object* v_a_2281_, lean_object* v_a_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2(v_a_2281_, v_a_2282_);
lean_dec(v_a_2281_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__3(lean_object* v_as_2284_, size_t v_sz_2285_, size_t v_i_2286_, lean_object* v_b_2287_){
_start:
{
uint8_t v___x_2288_; 
v___x_2288_ = lean_usize_dec_lt(v_i_2286_, v_sz_2285_);
if (v___x_2288_ == 0)
{
return v_b_2287_;
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2290_; 
v_a_2289_ = lean_array_uget_borrowed(v_as_2284_, v_i_2286_);
v___x_2290_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2(v_a_2289_, v_b_2287_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
return v_a_2291_;
}
else
{
lean_object* v_a_2292_; size_t v___x_2293_; size_t v___x_2294_; 
v_a_2292_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2292_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2293_ = ((size_t)1ULL);
v___x_2294_ = lean_usize_add(v_i_2286_, v___x_2293_);
v_i_2286_ = v___x_2294_;
v_b_2287_ = v_a_2292_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__3___boxed(lean_object* v_as_2296_, lean_object* v_sz_2297_, lean_object* v_i_2298_, lean_object* v_b_2299_){
_start:
{
size_t v_sz_boxed_2300_; size_t v_i_boxed_2301_; lean_object* v_res_2302_; 
v_sz_boxed_2300_ = lean_unbox_usize(v_sz_2297_);
lean_dec(v_sz_2297_);
v_i_boxed_2301_ = lean_unbox_usize(v_i_2298_);
lean_dec(v_i_2298_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__3(v_as_2296_, v_sz_boxed_2300_, v_i_boxed_2301_, v_b_2299_);
lean_dec_ref(v_as_2296_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___redArg(lean_object* v_upperBound_2303_, lean_object* v_p_2304_, lean_object* v_a_2305_, lean_object* v_b_2306_){
_start:
{
uint8_t v___x_2307_; 
v___x_2307_ = lean_nat_dec_lt(v_a_2305_, v_upperBound_2303_);
if (v___x_2307_ == 0)
{
lean_dec(v_a_2305_);
return v_b_2306_;
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2308_ = l_readSolution_x3f_readSolution(v_p_2304_, v_a_2305_, v_b_2306_);
v___x_2309_ = lean_unsigned_to_nat(1u);
v___x_2310_ = lean_nat_add(v_a_2305_, v___x_2309_);
lean_dec(v_a_2305_);
v_a_2305_ = v___x_2310_;
v_b_2306_ = v___x_2308_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___redArg___boxed(lean_object* v_upperBound_2312_, lean_object* v_p_2313_, lean_object* v_a_2314_, lean_object* v_b_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___redArg(v_upperBound_2312_, v_p_2313_, v_a_2314_, v_b_2315_);
lean_dec_ref(v_p_2313_);
lean_dec(v_upperBound_2312_);
return v_res_2316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00readSolution_x3f_spec__0(size_t v_sz_2317_, size_t v_i_2318_, lean_object* v_bs_2319_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_usize_dec_lt(v_i_2318_, v_sz_2317_);
if (v___x_2320_ == 0)
{
return v_bs_2319_;
}
else
{
lean_object* v_v_2321_; lean_object* v___x_2322_; lean_object* v_bs_x27_2323_; lean_object* v___y_2325_; 
v_v_2321_ = lean_array_uget(v_bs_2319_, v_i_2318_);
v___x_2322_ = lean_unsigned_to_nat(0u);
v_bs_x27_2323_ = lean_array_uset(v_bs_2319_, v_i_2318_, v___x_2322_);
if (lean_obj_tag(v_v_2321_) == 0)
{
lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2330_ = lean_obj_once(&l_Equation_normalize___closed__3, &l_Equation_normalize___closed__3_once, _init_l_Equation_normalize___closed__3);
v___x_2331_ = l_panic___at___00Std_DHashMap_Internal_AssocList_get_x21___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x21___at___00Equation_subst_spec__0_spec__0_spec__1(v___x_2330_);
v___y_2325_ = v___x_2331_;
goto v___jp_2324_;
}
else
{
lean_object* v_val_2332_; 
v_val_2332_ = lean_ctor_get(v_v_2321_, 0);
lean_inc(v_val_2332_);
lean_dec_ref_known(v_v_2321_, 1);
v___y_2325_ = v_val_2332_;
goto v___jp_2324_;
}
v___jp_2324_:
{
size_t v___x_2326_; size_t v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = ((size_t)1ULL);
v___x_2327_ = lean_usize_add(v_i_2318_, v___x_2326_);
v___x_2328_ = lean_array_uset(v_bs_x27_2323_, v_i_2318_, v___y_2325_);
v_i_2318_ = v___x_2327_;
v_bs_2319_ = v___x_2328_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00readSolution_x3f_spec__0___boxed(lean_object* v_sz_2333_, lean_object* v_i_2334_, lean_object* v_bs_2335_){
_start:
{
size_t v_sz_boxed_2336_; size_t v_i_boxed_2337_; lean_object* v_res_2338_; 
v_sz_boxed_2336_ = lean_unbox_usize(v_sz_2333_);
lean_dec(v_sz_2333_);
v_i_boxed_2337_ = lean_unbox_usize(v_i_2334_);
lean_dec(v_i_2334_);
v_res_2338_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00readSolution_x3f_spec__0(v_sz_boxed_2336_, v_i_boxed_2337_, v_bs_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__4(lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
if (lean_obj_tag(v_a_2339_) == 0)
{
lean_object* v___x_2341_; 
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_a_2340_);
return v___x_2341_;
}
else
{
lean_object* v_value_2342_; lean_object* v_coeffs_2343_; lean_object* v_tail_2344_; lean_object* v_size_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; 
lean_dec_ref(v_a_2340_);
v_value_2342_ = lean_ctor_get(v_a_2339_, 1);
v_coeffs_2343_ = lean_ctor_get(v_value_2342_, 1);
v_tail_2344_ = lean_ctor_get(v_a_2339_, 2);
v_size_2345_ = lean_ctor_get(v_coeffs_2343_, 0);
v___x_2346_ = lean_unsigned_to_nat(0u);
v___x_2347_ = lean_nat_dec_eq(v_size_2345_, v___x_2346_);
if (v___x_2347_ == 0)
{
lean_object* v___x_2348_; 
v___x_2348_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__2));
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; 
v___x_2349_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3));
v_a_2339_ = v_tail_2344_;
v_a_2340_ = v___x_2349_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__4___boxed(lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__4(v_a_2351_, v_a_2352_);
lean_dec(v_a_2351_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__5(lean_object* v_as_2354_, size_t v_sz_2355_, size_t v_i_2356_, lean_object* v_b_2357_){
_start:
{
uint8_t v___x_2358_; 
v___x_2358_ = lean_usize_dec_lt(v_i_2356_, v_sz_2355_);
if (v___x_2358_ == 0)
{
return v_b_2357_;
}
else
{
lean_object* v_a_2359_; lean_object* v___x_2360_; 
v_a_2359_ = lean_array_uget_borrowed(v_as_2354_, v_i_2356_);
v___x_2360_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__4(v_a_2359_, v_b_2357_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v_a_2361_; 
v_a_2361_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2361_);
lean_dec_ref_known(v___x_2360_, 1);
return v_a_2361_;
}
else
{
lean_object* v_a_2362_; size_t v___x_2363_; size_t v___x_2364_; 
v_a_2362_ = lean_ctor_get(v___x_2360_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2360_, 1);
v___x_2363_ = ((size_t)1ULL);
v___x_2364_ = lean_usize_add(v_i_2356_, v___x_2363_);
v_i_2356_ = v___x_2364_;
v_b_2357_ = v_a_2362_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__5___boxed(lean_object* v_as_2366_, lean_object* v_sz_2367_, lean_object* v_i_2368_, lean_object* v_b_2369_){
_start:
{
size_t v_sz_boxed_2370_; size_t v_i_boxed_2371_; lean_object* v_res_2372_; 
v_sz_boxed_2370_ = lean_unbox_usize(v_sz_2367_);
lean_dec(v_sz_2367_);
v_i_boxed_2371_ = lean_unbox_usize(v_i_2368_);
lean_dec(v_i_2368_);
v_res_2372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__5(v_as_2366_, v_sz_boxed_2370_, v_i_boxed_2371_, v_b_2369_);
lean_dec_ref(v_as_2366_);
return v_res_2372_;
}
}
LEAN_EXPORT lean_object* l_readSolution_x3f(lean_object* v_p_2375_){
_start:
{
lean_object* v_equations_2376_; lean_object* v_nVars_2377_; lean_object* v_buckets_2388_; lean_object* v___x_2398_; lean_object* v___x_2399_; size_t v_sz_2400_; size_t v___x_2401_; lean_object* v___x_2402_; lean_object* v_fst_2403_; 
v_equations_2376_ = lean_ctor_get(v_p_2375_, 0);
v_nVars_2377_ = lean_ctor_get(v_p_2375_, 3);
lean_inc(v_nVars_2377_);
v_buckets_2388_ = lean_ctor_get(v_equations_2376_, 1);
v___x_2398_ = lean_box(0);
v___x_2399_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3));
v_sz_2400_ = lean_array_size(v_buckets_2388_);
v___x_2401_ = ((size_t)0ULL);
v___x_2402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__5(v_buckets_2388_, v_sz_2400_, v___x_2401_, v___x_2399_);
v_fst_2403_ = lean_ctor_get(v___x_2402_, 0);
lean_inc(v_fst_2403_);
lean_dec_ref(v___x_2402_);
if (lean_obj_tag(v_fst_2403_) == 0)
{
goto v___jp_2389_;
}
else
{
lean_object* v_val_2404_; uint8_t v___x_2405_; 
v_val_2404_ = lean_ctor_get(v_fst_2403_, 0);
lean_inc(v_val_2404_);
lean_dec_ref_known(v_fst_2403_, 1);
v___x_2405_ = lean_unbox(v_val_2404_);
lean_dec(v_val_2404_);
if (v___x_2405_ == 0)
{
goto v___jp_2389_;
}
else
{
lean_dec(v_nVars_2377_);
lean_dec_ref(v_p_2375_);
return v___x_2398_;
}
}
v___jp_2378_:
{
lean_object* v___x_2379_; lean_object* v_assignment_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; size_t v_sz_2383_; size_t v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2379_ = lean_box(0);
lean_inc(v_nVars_2377_);
v_assignment_2380_ = lean_mk_array(v_nVars_2377_, v___x_2379_);
v___x_2381_ = lean_unsigned_to_nat(0u);
v___x_2382_ = l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___redArg(v_nVars_2377_, v_p_2375_, v___x_2381_, v_assignment_2380_);
lean_dec_ref(v_p_2375_);
lean_dec(v_nVars_2377_);
v_sz_2383_ = lean_array_size(v___x_2382_);
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00readSolution_x3f_spec__0(v_sz_2383_, v___x_2384_, v___x_2382_);
v___x_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2386_, 0, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2386_);
return v___x_2387_;
}
v___jp_2389_:
{
lean_object* v___x_2390_; size_t v_sz_2391_; size_t v___x_2392_; lean_object* v___x_2393_; lean_object* v_fst_2394_; 
v___x_2390_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3));
v_sz_2391_ = lean_array_size(v_buckets_2388_);
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00readSolution_x3f_spec__3(v_buckets_2388_, v_sz_2391_, v___x_2392_, v___x_2390_);
v_fst_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_fst_2394_);
lean_dec_ref(v___x_2393_);
if (lean_obj_tag(v_fst_2394_) == 0)
{
goto v___jp_2378_;
}
else
{
lean_object* v_val_2395_; uint8_t v___x_2396_; 
v_val_2395_ = lean_ctor_get(v_fst_2394_, 0);
lean_inc(v_val_2395_);
lean_dec_ref_known(v_fst_2394_, 1);
v___x_2396_ = lean_unbox(v_val_2395_);
lean_dec(v_val_2395_);
if (v___x_2396_ == 0)
{
goto v___jp_2378_;
}
else
{
lean_object* v___x_2397_; 
lean_dec(v_nVars_2377_);
lean_dec_ref(v_p_2375_);
v___x_2397_ = ((lean_object*)(l_readSolution_x3f___closed__0));
return v___x_2397_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1(lean_object* v_upperBound_2406_, lean_object* v_p_2407_, lean_object* v_inst_2408_, lean_object* v_R_2409_, lean_object* v_a_2410_, lean_object* v_b_2411_, lean_object* v_c_2412_){
_start:
{
lean_object* v___x_2413_; 
v___x_2413_ = l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___redArg(v_upperBound_2406_, v_p_2407_, v_a_2410_, v_b_2411_);
return v___x_2413_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1___boxed(lean_object* v_upperBound_2414_, lean_object* v_p_2415_, lean_object* v_inst_2416_, lean_object* v_R_2417_, lean_object* v_a_2418_, lean_object* v_b_2419_, lean_object* v_c_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_WellFounded_opaqueFix_u2083___at___00readSolution_x3f_spec__1(v_upperBound_2414_, v_p_2415_, v_inst_2416_, v_R_2417_, v_a_2418_, v_b_2419_, v_c_2420_);
lean_dec_ref(v_p_2415_);
lean_dec(v_upperBound_2414_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_solveProblem_x27(lean_object* v_p_2422_){
_start:
{
lean_object* v___x_2423_; 
lean_inc_ref(v_p_2422_);
v___x_2423_ = l_readSolution_x3f(v_p_2422_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_p_2424_; lean_object* v___x_2425_; 
v_p_2424_ = l_eliminateSingletons(v_p_2422_);
lean_inc_ref(v_p_2424_);
v___x_2425_ = l_readSolution_x3f(v_p_2424_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_p_2426_; 
v_p_2426_ = l_addAuxEquation(v_p_2424_);
v_p_2422_ = v_p_2426_;
goto _start;
}
else
{
lean_object* v_val_2428_; 
lean_dec_ref(v_p_2424_);
v_val_2428_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_val_2428_);
lean_dec_ref_known(v___x_2425_, 1);
return v_val_2428_;
}
}
else
{
lean_object* v_val_2429_; 
lean_dec_ref(v_p_2422_);
v_val_2429_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_val_2429_);
lean_dec_ref_known(v___x_2423_, 1);
return v_val_2429_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__0(lean_object* v_assignment_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_){
_start:
{
if (lean_obj_tag(v_a_2431_) == 0)
{
lean_object* v___x_2433_; 
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2432_);
return v___x_2433_;
}
else
{
lean_object* v_key_2434_; lean_object* v_value_2435_; lean_object* v_tail_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_key_2434_ = lean_ctor_get(v_a_2431_, 0);
v_value_2435_ = lean_ctor_get(v_a_2431_, 1);
v_tail_2436_ = lean_ctor_get(v_a_2431_, 2);
v___x_2437_ = l_Int_instInhabited;
v___x_2438_ = lean_array_get_borrowed(v___x_2437_, v_assignment_2430_, v_key_2434_);
v___x_2439_ = lean_int_mul(v_value_2435_, v___x_2438_);
v___x_2440_ = lean_int_add(v_a_2432_, v___x_2439_);
lean_dec(v___x_2439_);
lean_dec(v_a_2432_);
v_a_2431_ = v_tail_2436_;
v_a_2432_ = v___x_2440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__0___boxed(lean_object* v_assignment_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__0(v_assignment_2442_, v_a_2443_, v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_assignment_2442_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__1(lean_object* v_assignment_2446_, lean_object* v_as_2447_, size_t v_sz_2448_, size_t v_i_2449_, lean_object* v_b_2450_){
_start:
{
uint8_t v___x_2451_; 
v___x_2451_ = lean_usize_dec_lt(v_i_2449_, v_sz_2448_);
if (v___x_2451_ == 0)
{
return v_b_2450_;
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2453_; 
v_a_2452_ = lean_array_uget_borrowed(v_as_2447_, v_i_2449_);
v___x_2453_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__0(v_assignment_2446_, v_a_2452_, v_b_2450_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
return v_a_2454_;
}
else
{
lean_object* v_a_2455_; size_t v___x_2456_; size_t v___x_2457_; 
v_a_2455_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2456_ = ((size_t)1ULL);
v___x_2457_ = lean_usize_add(v_i_2449_, v___x_2456_);
v_i_2449_ = v___x_2457_;
v_b_2450_ = v_a_2455_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__1___boxed(lean_object* v_assignment_2459_, lean_object* v_as_2460_, lean_object* v_sz_2461_, lean_object* v_i_2462_, lean_object* v_b_2463_){
_start:
{
size_t v_sz_boxed_2464_; size_t v_i_boxed_2465_; lean_object* v_res_2466_; 
v_sz_boxed_2464_ = lean_unbox_usize(v_sz_2461_);
lean_dec(v_sz_2461_);
v_i_boxed_2465_ = lean_unbox_usize(v_i_2462_);
lean_dec(v_i_2462_);
v_res_2466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__1(v_assignment_2459_, v_as_2460_, v_sz_boxed_2464_, v_i_boxed_2465_, v_b_2463_);
lean_dec_ref(v_as_2460_);
lean_dec_ref(v_assignment_2459_);
return v_res_2466_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__2(lean_object* v_assignment_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
if (lean_obj_tag(v_a_2468_) == 0)
{
lean_object* v___x_2470_; 
v___x_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2470_, 0, v_a_2469_);
return v___x_2470_;
}
else
{
lean_object* v_value_2471_; lean_object* v_coeffs_2472_; lean_object* v_tail_2473_; lean_object* v_const_2474_; lean_object* v_buckets_2475_; lean_object* v_r_2476_; size_t v_sz_2477_; size_t v___x_2478_; lean_object* v___x_2479_; uint8_t v___x_2480_; 
lean_dec_ref(v_a_2469_);
v_value_2471_ = lean_ctor_get(v_a_2468_, 1);
v_coeffs_2472_ = lean_ctor_get(v_value_2471_, 1);
v_tail_2473_ = lean_ctor_get(v_a_2468_, 2);
v_const_2474_ = lean_ctor_get(v_value_2471_, 2);
v_buckets_2475_ = lean_ctor_get(v_coeffs_2472_, 1);
v_r_2476_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v_sz_2477_ = lean_array_size(v_buckets_2475_);
v___x_2478_ = ((size_t)0ULL);
v___x_2479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__1(v_assignment_2467_, v_buckets_2475_, v_sz_2477_, v___x_2478_, v_r_2476_);
v___x_2480_ = lean_int_dec_eq(v___x_2479_, v_const_2474_);
lean_dec(v___x_2479_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
v___x_2481_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__2));
return v___x_2481_;
}
else
{
lean_object* v___x_2482_; 
v___x_2482_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3));
v_a_2468_ = v_tail_2473_;
v_a_2469_ = v___x_2482_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__2___boxed(lean_object* v_assignment_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__2(v_assignment_2484_, v_a_2485_, v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_assignment_2484_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__3(lean_object* v_assignment_2488_, lean_object* v_as_2489_, size_t v_sz_2490_, size_t v_i_2491_, lean_object* v_b_2492_){
_start:
{
uint8_t v___x_2493_; 
v___x_2493_ = lean_usize_dec_lt(v_i_2491_, v_sz_2490_);
if (v___x_2493_ == 0)
{
return v_b_2492_;
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2495_; 
v_a_2494_ = lean_array_uget_borrowed(v_as_2489_, v_i_2491_);
v___x_2495_ = l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00isSatAssignment_spec__2(v_assignment_2488_, v_a_2494_, v_b_2492_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
return v_a_2496_;
}
else
{
lean_object* v_a_2497_; size_t v___x_2498_; size_t v___x_2499_; 
v_a_2497_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2498_ = ((size_t)1ULL);
v___x_2499_ = lean_usize_add(v_i_2491_, v___x_2498_);
v_i_2491_ = v___x_2499_;
v_b_2492_ = v_a_2497_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__3___boxed(lean_object* v_assignment_2501_, lean_object* v_as_2502_, lean_object* v_sz_2503_, lean_object* v_i_2504_, lean_object* v_b_2505_){
_start:
{
size_t v_sz_boxed_2506_; size_t v_i_boxed_2507_; lean_object* v_res_2508_; 
v_sz_boxed_2506_ = lean_unbox_usize(v_sz_2503_);
lean_dec(v_sz_2503_);
v_i_boxed_2507_ = lean_unbox_usize(v_i_2504_);
lean_dec(v_i_2504_);
v_res_2508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__3(v_assignment_2501_, v_as_2502_, v_sz_boxed_2506_, v_i_boxed_2507_, v_b_2505_);
lean_dec_ref(v_as_2502_);
lean_dec_ref(v_assignment_2501_);
return v_res_2508_;
}
}
LEAN_EXPORT uint8_t l_isSatAssignment(lean_object* v_p_2509_, lean_object* v_assignment_2510_){
_start:
{
lean_object* v_equations_2511_; lean_object* v_buckets_2512_; lean_object* v___x_2513_; size_t v_sz_2514_; size_t v___x_2515_; lean_object* v___x_2516_; lean_object* v_fst_2517_; 
v_equations_2511_ = lean_ctor_get(v_p_2509_, 0);
v_buckets_2512_ = lean_ctor_get(v_equations_2511_, 1);
v___x_2513_ = ((lean_object*)(l___private_Std_Data_DHashMap_Internal_AssocList_Basic_0__Std_DHashMap_Internal_AssocList_forInStep_go___at___00readSolution_x3f_spec__2___closed__3));
v_sz_2514_ = lean_array_size(v_buckets_2512_);
v___x_2515_ = ((size_t)0ULL);
v___x_2516_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00isSatAssignment_spec__3(v_assignment_2510_, v_buckets_2512_, v_sz_2514_, v___x_2515_, v___x_2513_);
v_fst_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_fst_2517_);
lean_dec_ref(v___x_2516_);
if (lean_obj_tag(v_fst_2517_) == 0)
{
uint8_t v___x_2518_; 
v___x_2518_ = 1;
return v___x_2518_;
}
else
{
lean_object* v_val_2519_; uint8_t v___x_2520_; 
v_val_2519_ = lean_ctor_get(v_fst_2517_, 0);
lean_inc(v_val_2519_);
lean_dec_ref_known(v_fst_2517_, 1);
v___x_2520_ = lean_unbox(v_val_2519_);
lean_dec(v_val_2519_);
if (v___x_2520_ == 0)
{
uint8_t v___x_2521_; 
v___x_2521_ = 1;
return v___x_2521_;
}
else
{
uint8_t v___x_2522_; 
v___x_2522_ = 0;
return v___x_2522_;
}
}
}
}
LEAN_EXPORT lean_object* l_isSatAssignment___boxed(lean_object* v_p_2523_, lean_object* v_assignment_2524_){
_start:
{
uint8_t v_res_2525_; lean_object* v_r_2526_; 
v_res_2525_ = l_isSatAssignment(v_p_2523_, v_assignment_2524_);
lean_dec_ref(v_assignment_2524_);
lean_dec_ref(v_p_2523_);
v_r_2526_ = lean_box(v_res_2525_);
return v_r_2526_;
}
}
LEAN_EXPORT lean_object* l_solveProblem(lean_object* v_p_2527_){
_start:
{
lean_object* v_nVars_2528_; lean_object* v___x_2529_; 
v_nVars_2528_ = lean_ctor_get(v_p_2527_, 3);
lean_inc_ref(v_p_2527_);
v___x_2529_ = l_solveProblem_x27(v_p_2527_);
if (lean_obj_tag(v___x_2529_) == 0)
{
lean_dec_ref(v_p_2527_);
return v___x_2529_;
}
else
{
lean_object* v_assignment_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2541_; 
v_assignment_2530_ = lean_ctor_get(v___x_2529_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v___x_2529_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2532_ = v___x_2529_;
v_isShared_2533_ = v_isSharedCheck_2541_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_assignment_2530_);
lean_dec(v___x_2529_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2541_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v_assignment_x27_2535_; uint8_t v___x_2536_; 
v___x_2534_ = lean_unsigned_to_nat(0u);
lean_inc(v_nVars_2528_);
v_assignment_x27_2535_ = l_Array_extract___redArg(v_assignment_2530_, v___x_2534_, v_nVars_2528_);
lean_dec_ref(v_assignment_2530_);
v___x_2536_ = l_isSatAssignment(v_p_2527_, v_assignment_x27_2535_);
lean_dec_ref(v_p_2527_);
if (v___x_2536_ == 0)
{
lean_object* v___x_2537_; 
lean_dec_ref(v_assignment_x27_2535_);
lean_del_object(v___x_2532_);
v___x_2537_ = lean_box(0);
return v___x_2537_;
}
else
{
lean_object* v___x_2539_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 0, v_assignment_x27_2535_);
v___x_2539_ = v___x_2532_;
goto v_reusejp_2538_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_assignment_x27_2535_);
v___x_2539_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2538_;
}
v_reusejp_2538_:
{
return v___x_2539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_error___redArg(lean_object* v_msg_2544_){
_start:
{
lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; 
v___x_2546_ = ((lean_object*)(l_error___redArg___closed__0));
v___x_2547_ = lean_string_append(v___x_2546_, v_msg_2544_);
v___x_2548_ = ((lean_object*)(l_error___redArg___closed__1));
v___x_2549_ = lean_string_append(v___x_2547_, v___x_2548_);
v___x_2550_ = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
v___x_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
return v___x_2551_;
}
}
LEAN_EXPORT lean_object* l_error___redArg___boxed(lean_object* v_msg_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l_error___redArg(v_msg_2552_);
lean_dec_ref(v_msg_2552_);
return v_res_2554_;
}
}
LEAN_EXPORT lean_object* l_error(lean_object* v_00_u03b1_2555_, lean_object* v_msg_2556_){
_start:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_error___redArg(v_msg_2556_);
return v___x_2558_;
}
}
LEAN_EXPORT lean_object* l_error___boxed(lean_object* v_00_u03b1_2559_, lean_object* v_msg_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_error(v_00_u03b1_2559_, v_msg_2560_);
lean_dec_ref(v_msg_2560_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_Array_ithVal(lean_object* v_xs_2567_, lean_object* v_i_2568_, lean_object* v_name_2569_){
_start:
{
lean_object* v___x_2571_; uint8_t v___x_2572_; 
v___x_2571_ = lean_array_get_size(v_xs_2567_);
v___x_2572_ = lean_nat_dec_lt(v_i_2568_, v___x_2571_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2573_ = ((lean_object*)(l_Array_ithVal___closed__0));
v___x_2574_ = lean_string_append(v___x_2573_, v_name_2569_);
v___x_2575_ = l_error___redArg(v___x_2574_);
lean_dec_ref(v___x_2574_);
return v___x_2575_;
}
else
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2576_ = lean_array_fget_borrowed(v_xs_2567_, v_i_2568_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_string_utf8_byte_size(v___x_2576_);
lean_inc(v___x_2576_);
v___x_2579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2576_);
lean_ctor_set(v___x_2579_, 1, v___x_2577_);
lean_ctor_set(v___x_2579_, 2, v___x_2578_);
v___x_2580_ = l_String_Slice_toInt_x3f(v___x_2579_);
if (lean_obj_tag(v___x_2580_) == 1)
{
lean_object* v_val_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
v_val_2581_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2580_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_val_2581_);
lean_dec(v___x_2580_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
lean_ctor_set_tag(v___x_2583_, 0);
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_val_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
else
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; 
lean_dec(v___x_2580_);
v___x_2589_ = ((lean_object*)(l_Array_ithVal___closed__1));
v___x_2590_ = lean_string_append(v___x_2589_, v_name_2569_);
v___x_2591_ = ((lean_object*)(l_Array_ithVal___closed__2));
v___x_2592_ = lean_string_append(v___x_2590_, v___x_2591_);
v___x_2593_ = lean_string_append(v___x_2592_, v___x_2576_);
v___x_2594_ = ((lean_object*)(l_Array_ithVal___closed__3));
v___x_2595_ = lean_string_append(v___x_2593_, v___x_2594_);
v___x_2596_ = l_error___redArg(v___x_2595_);
lean_dec_ref(v___x_2595_);
return v___x_2596_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_ithVal___boxed(lean_object* v_xs_2597_, lean_object* v_i_2598_, lean_object* v_name_2599_, lean_object* v_a_2600_){
_start:
{
lean_object* v_res_2601_; 
v_res_2601_ = l_Array_ithVal(v_xs_2597_, v_i_2598_, v_name_2599_);
lean_dec_ref(v_name_2599_);
lean_dec(v_i_2598_);
lean_dec_ref(v_xs_2597_);
return v_res_2601_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2___redArg(lean_object* v_a_2602_, lean_object* v_f_2603_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = lean_apply_1(v_a_2602_, lean_box(0));
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2610_; lean_object* v___x_2612_; 
v___x_2610_ = lean_apply_1(v_f_2603_, v_a_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v___x_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v___x_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec(v_f_2603_);
v_a_2615_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2605_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2605_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2___redArg___boxed(lean_object* v_a_2623_, lean_object* v_f_2624_, lean_object* v___y_2625_){
_start:
{
lean_object* v_res_2626_; 
v_res_2626_ = l_Functor_mapRev___at___00main_spec__2___redArg(v_a_2623_, v_f_2624_);
return v_res_2626_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2(lean_object* v_00_u03b1_2627_, lean_object* v_00_u03b2_2628_, lean_object* v_a_2629_, lean_object* v_f_2630_){
_start:
{
lean_object* v___x_2632_; 
v___x_2632_ = l_Functor_mapRev___at___00main_spec__2___redArg(v_a_2629_, v_f_2630_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___at___00main_spec__2___boxed(lean_object* v_00_u03b1_2633_, lean_object* v_00_u03b2_2634_, lean_object* v_a_2635_, lean_object* v_f_2636_, lean_object* v___y_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Functor_mapRev___at___00main_spec__2(v_00_u03b1_2633_, v_00_u03b2_2634_, v_a_2635_, v_f_2636_);
return v_res_2638_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__0(lean_object* v_as_2639_, size_t v_i_2640_, size_t v_stop_2641_, lean_object* v_b_2642_){
_start:
{
lean_object* v___y_2644_; uint8_t v___x_2648_; 
v___x_2648_ = lean_usize_dec_eq(v_i_2640_, v_stop_2641_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2652_; lean_object* v___x_2653_; uint8_t v___x_2654_; 
v___x_2649_ = lean_array_uget_borrowed(v_as_2639_, v_i_2640_);
v___x_2652_ = lean_string_utf8_byte_size(v___x_2649_);
v___x_2653_ = lean_unsigned_to_nat(0u);
v___x_2654_ = lean_nat_dec_eq(v___x_2652_, v___x_2653_);
if (v___x_2654_ == 0)
{
goto v___jp_2650_;
}
else
{
if (v___x_2648_ == 0)
{
v___y_2644_ = v_b_2642_;
goto v___jp_2643_;
}
else
{
goto v___jp_2650_;
}
}
v___jp_2650_:
{
lean_object* v___x_2651_; 
lean_inc(v___x_2649_);
v___x_2651_ = lean_array_push(v_b_2642_, v___x_2649_);
v___y_2644_ = v___x_2651_;
goto v___jp_2643_;
}
}
else
{
return v_b_2642_;
}
v___jp_2643_:
{
size_t v___x_2645_; size_t v___x_2646_; 
v___x_2645_ = ((size_t)1ULL);
v___x_2646_ = lean_usize_add(v_i_2640_, v___x_2645_);
v_i_2640_ = v___x_2646_;
v_b_2642_ = v___y_2644_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__0___boxed(lean_object* v_as_2655_, lean_object* v_i_2656_, lean_object* v_stop_2657_, lean_object* v_b_2658_){
_start:
{
size_t v_i_boxed_2659_; size_t v_stop_boxed_2660_; lean_object* v_res_2661_; 
v_i_boxed_2659_ = lean_unbox_usize(v_i_2656_);
lean_dec(v_i_2656_);
v_stop_boxed_2660_ = lean_unbox_usize(v_stop_2657_);
lean_dec(v_stop_2657_);
v_res_2661_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__0(v_as_2655_, v_i_boxed_2659_, v_stop_boxed_2660_, v_b_2658_);
lean_dec_ref(v_as_2655_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_main___lam__0(lean_object* v_as_2664_){
_start:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2665_ = lean_unsigned_to_nat(0u);
v___x_2666_ = lean_array_get_size(v_as_2664_);
v___x_2667_ = ((lean_object*)(l_main___lam__0___closed__0));
v___x_2668_ = lean_nat_dec_lt(v___x_2665_, v___x_2666_);
if (v___x_2668_ == 0)
{
return v___x_2667_;
}
else
{
uint8_t v___x_2669_; 
v___x_2669_ = lean_nat_dec_le(v___x_2666_, v___x_2666_);
if (v___x_2669_ == 0)
{
if (v___x_2668_ == 0)
{
return v___x_2667_;
}
else
{
size_t v___x_2670_; size_t v___x_2671_; lean_object* v___x_2672_; 
v___x_2670_ = ((size_t)0ULL);
v___x_2671_ = lean_usize_of_nat(v___x_2666_);
v___x_2672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__0(v_as_2664_, v___x_2670_, v___x_2671_, v___x_2667_);
return v___x_2672_;
}
}
else
{
size_t v___x_2673_; size_t v___x_2674_; lean_object* v___x_2675_; 
v___x_2673_ = ((size_t)0ULL);
v___x_2674_ = lean_usize_of_nat(v___x_2666_);
v___x_2675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00main_spec__0(v_as_2664_, v___x_2673_, v___x_2674_, v___x_2667_);
return v___x_2675_;
}
}
}
}
LEAN_EXPORT lean_object* l_main___lam__0___boxed(lean_object* v_as_2676_){
_start:
{
lean_object* v_res_2677_; 
v_res_2677_ = l_main___lam__0(v_as_2676_);
lean_dec_ref(v_as_2676_);
return v_res_2677_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___lam__0(lean_object* v___x_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v___x_2681_, lean_object* v_b_2682_, lean_object* v_____r_2683_){
_start:
{
lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = lean_nat_to_int(v___x_2678_);
v___x_2686_ = lean_int_dec_eq(v_a_2679_, v___x_2685_);
lean_dec(v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v___x_2687_ = l_Int_toNat(v_a_2680_);
v___x_2688_ = lean_nat_sub(v___x_2687_, v___x_2681_);
lean_dec(v___x_2687_);
v___x_2689_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_b_2682_, v___x_2688_, v_a_2679_);
v___x_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2690_, 0, v___x_2689_);
v___x_2691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2691_, 0, v___x_2690_);
return v___x_2691_;
}
else
{
lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec(v_a_2679_);
v___x_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2692_, 0, v_b_2682_);
v___x_2693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2692_);
return v___x_2693_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___lam__0___boxed(lean_object* v___x_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v___x_2697_, lean_object* v_b_2698_, lean_object* v_____r_2699_, lean_object* v___y_2700_){
_start:
{
lean_object* v_res_2701_; 
v_res_2701_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___lam__0(v___x_2694_, v_a_2695_, v_a_2696_, v___x_2697_, v_b_2698_, v_____r_2699_);
lean_dec(v___x_2697_);
lean_dec(v_a_2696_);
return v_res_2701_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg(lean_object* v___x_2705_, lean_object* v_a_2706_, lean_object* v_b_2707_){
_start:
{
lean_object* v_inner_2709_; lean_object* v_next_2710_; 
v_inner_2709_ = lean_ctor_get(v_a_2706_, 2);
lean_inc(v_inner_2709_);
v_next_2710_ = lean_ctor_get(v_inner_2709_, 0);
lean_inc(v_next_2710_);
if (lean_obj_tag(v_next_2710_) == 0)
{
lean_object* v___x_2711_; 
lean_dec(v_inner_2709_);
lean_dec_ref(v_a_2706_);
v___x_2711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_b_2707_);
return v___x_2711_;
}
else
{
lean_object* v_nextIdx_2712_; lean_object* v_n_2713_; lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2802_; 
v_nextIdx_2712_ = lean_ctor_get(v_a_2706_, 0);
v_n_2713_ = lean_ctor_get(v_a_2706_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_a_2706_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v_a_2706_, 2);
lean_dec(v_unused_2803_);
v___x_2715_ = v_a_2706_;
v_isShared_2716_ = v_isSharedCheck_2802_;
goto v_resetjp_2714_;
}
else
{
lean_inc(v_n_2713_);
lean_inc(v_nextIdx_2712_);
lean_dec(v_a_2706_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2802_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v_upperBound_2717_; lean_object* v___x_2719_; uint8_t v_isShared_2720_; uint8_t v_isSharedCheck_2800_; 
v_upperBound_2717_ = lean_ctor_get(v_inner_2709_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_inner_2709_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; 
v_unused_2801_ = lean_ctor_get(v_inner_2709_, 0);
lean_dec(v_unused_2801_);
v___x_2719_ = v_inner_2709_;
v_isShared_2720_ = v_isSharedCheck_2800_;
goto v_resetjp_2718_;
}
else
{
lean_inc(v_upperBound_2717_);
lean_dec(v_inner_2709_);
v___x_2719_ = lean_box(0);
v_isShared_2720_ = v_isSharedCheck_2800_;
goto v_resetjp_2718_;
}
v_resetjp_2718_:
{
lean_object* v_val_2721_; lean_object* v___x_2723_; uint8_t v_isShared_2724_; uint8_t v_isSharedCheck_2799_; 
v_val_2721_ = lean_ctor_get(v_next_2710_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v_next_2710_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2723_ = v_next_2710_;
v_isShared_2724_ = v_isSharedCheck_2799_;
goto v_resetjp_2722_;
}
else
{
lean_inc(v_val_2721_);
lean_dec(v_next_2710_);
v___x_2723_ = lean_box(0);
v_isShared_2724_ = v_isSharedCheck_2799_;
goto v_resetjp_2722_;
}
v_resetjp_2722_:
{
lean_object* v___x_2725_; uint8_t v___x_2726_; 
v___x_2725_ = lean_nat_add(v_val_2721_, v_nextIdx_2712_);
lean_dec(v_nextIdx_2712_);
lean_dec(v_val_2721_);
v___x_2726_ = lean_nat_dec_lt(v___x_2725_, v_upperBound_2717_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
lean_dec(v___x_2725_);
lean_del_object(v___x_2723_);
lean_del_object(v___x_2719_);
lean_dec(v_upperBound_2717_);
lean_del_object(v___x_2715_);
lean_dec(v_n_2713_);
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_b_2707_);
return v___x_2727_;
}
else
{
lean_object* v___x_2728_; lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2728_ = lean_unsigned_to_nat(1u);
v___x_2729_ = lean_nat_add(v___x_2725_, v___x_2728_);
lean_inc(v___x_2729_);
if (v_isShared_2724_ == 0)
{
lean_ctor_set(v___x_2723_, 0, v___x_2729_);
v___x_2731_ = v___x_2723_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
lean_object* v___x_2733_; 
if (v_isShared_2720_ == 0)
{
lean_ctor_set(v___x_2719_, 0, v___x_2731_);
v___x_2733_ = v___x_2719_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2797_, 1, v_upperBound_2717_);
v___x_2733_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2735_; 
lean_inc(v_n_2713_);
if (v_isShared_2716_ == 0)
{
lean_ctor_set(v___x_2715_, 2, v___x_2733_);
lean_ctor_set(v___x_2715_, 0, v_n_2713_);
v___x_2735_ = v___x_2715_;
goto v_reusejp_2734_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_n_2713_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_n_2713_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v___x_2733_);
v___x_2735_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2734_;
}
v_reusejp_2734_:
{
lean_object* v___y_2737_; lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__0));
v___x_2758_ = l_Array_ithVal(v___x_2705_, v___x_2725_, v___x_2757_);
lean_dec(v___x_2725_);
if (lean_obj_tag(v___x_2758_) == 0)
{
lean_object* v_a_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
lean_inc(v_a_2759_);
lean_dec_ref_known(v___x_2758_, 1);
v___x_2760_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__1));
v___x_2761_ = l_Array_ithVal(v___x_2705_, v___x_2729_, v___x_2760_);
lean_dec(v___x_2729_);
if (lean_obj_tag(v___x_2761_) == 0)
{
lean_object* v_a_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_a_2762_ = lean_ctor_get(v___x_2761_, 0);
lean_inc(v_a_2762_);
lean_dec_ref_known(v___x_2761_, 1);
v___x_2763_ = lean_unsigned_to_nat(0u);
v___x_2764_ = lean_obj_once(&l_Int_roundedDiv___closed__2, &l_Int_roundedDiv___closed__2_once, _init_l_Int_roundedDiv___closed__2);
v___x_2765_ = lean_int_dec_lt(v_a_2762_, v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = lean_box(0);
v___x_2767_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___lam__0(v___x_2763_, v_a_2759_, v_a_2762_, v___x_2728_, v_b_2707_, v___x_2766_);
lean_dec(v_a_2762_);
v___y_2737_ = v___x_2767_;
goto v___jp_2736_;
}
else
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___closed__2));
v___x_2769_ = l_error___redArg(v___x_2768_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; lean_object* v___x_2771_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___lam__0(v___x_2763_, v_a_2759_, v_a_2762_, v___x_2728_, v_b_2707_, v_a_2770_);
lean_dec(v_a_2762_);
v___y_2737_ = v___x_2771_;
goto v___jp_2736_;
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec(v_a_2762_);
lean_dec(v_a_2759_);
lean_dec_ref(v___x_2735_);
lean_dec_ref(v_b_2707_);
v_a_2772_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2769_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2769_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
}
else
{
lean_object* v_a_2780_; lean_object* v___x_2782_; uint8_t v_isShared_2783_; uint8_t v_isSharedCheck_2787_; 
lean_dec(v_a_2759_);
lean_dec_ref(v___x_2735_);
lean_dec_ref(v_b_2707_);
v_a_2780_ = lean_ctor_get(v___x_2761_, 0);
v_isSharedCheck_2787_ = !lean_is_exclusive(v___x_2761_);
if (v_isSharedCheck_2787_ == 0)
{
v___x_2782_ = v___x_2761_;
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
else
{
lean_inc(v_a_2780_);
lean_dec(v___x_2761_);
v___x_2782_ = lean_box(0);
v_isShared_2783_ = v_isSharedCheck_2787_;
goto v_resetjp_2781_;
}
v_resetjp_2781_:
{
lean_object* v___x_2785_; 
if (v_isShared_2783_ == 0)
{
v___x_2785_ = v___x_2782_;
goto v_reusejp_2784_;
}
else
{
lean_object* v_reuseFailAlloc_2786_; 
v_reuseFailAlloc_2786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2786_, 0, v_a_2780_);
v___x_2785_ = v_reuseFailAlloc_2786_;
goto v_reusejp_2784_;
}
v_reusejp_2784_:
{
return v___x_2785_;
}
}
}
}
else
{
lean_object* v_a_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
lean_dec_ref(v___x_2735_);
lean_dec(v___x_2729_);
lean_dec_ref(v_b_2707_);
v_a_2788_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2795_ == 0)
{
v___x_2790_ = v___x_2758_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_inc(v_a_2788_);
lean_dec(v___x_2758_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2788_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
v___jp_2736_:
{
if (lean_obj_tag(v___y_2737_) == 0)
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2748_; 
v_a_2738_ = lean_ctor_get(v___y_2737_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___y_2737_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2740_ = v___y_2737_;
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___y_2737_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2748_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
if (lean_obj_tag(v_a_2738_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2744_; 
lean_dec_ref(v___x_2735_);
v_a_2742_ = lean_ctor_get(v_a_2738_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v_a_2738_, 1);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v_a_2742_);
v___x_2744_ = v___x_2740_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2742_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
else
{
lean_object* v_a_2746_; 
lean_del_object(v___x_2740_);
v_a_2746_ = lean_ctor_get(v_a_2738_, 0);
lean_inc(v_a_2746_);
lean_dec_ref_known(v_a_2738_, 1);
v_a_2706_ = v___x_2735_;
v_b_2707_ = v_a_2746_;
goto _start;
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2756_; 
lean_dec_ref(v___x_2735_);
v_a_2749_ = lean_ctor_get(v___y_2737_, 0);
v_isSharedCheck_2756_ = !lean_is_exclusive(v___y_2737_);
if (v_isSharedCheck_2756_ == 0)
{
v___x_2751_ = v___y_2737_;
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___y_2737_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2756_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v___x_2754_; 
if (v_isShared_2752_ == 0)
{
v___x_2754_ = v___x_2751_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_a_2749_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg___boxed(lean_object* v___x_2804_, lean_object* v_a_2805_, lean_object* v_b_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg(v___x_2804_, v_a_2805_, v_b_2806_);
lean_dec_ref(v___x_2804_);
return v_res_2808_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg(lean_object* v_a_2816_, lean_object* v_b_2817_){
_start:
{
lean_object* v_array_2819_; lean_object* v_start_2820_; lean_object* v_stop_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2909_; 
v_array_2819_ = lean_ctor_get(v_a_2816_, 0);
v_start_2820_ = lean_ctor_get(v_a_2816_, 1);
v_stop_2821_ = lean_ctor_get(v_a_2816_, 2);
v_isSharedCheck_2909_ = !lean_is_exclusive(v_a_2816_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2823_ = v_a_2816_;
v_isShared_2824_ = v_isSharedCheck_2909_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_stop_2821_);
lean_inc(v_start_2820_);
lean_inc(v_array_2819_);
lean_dec(v_a_2816_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2909_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
uint8_t v___x_2825_; 
v___x_2825_ = lean_nat_dec_lt(v_start_2820_, v_stop_2821_);
if (v___x_2825_ == 0)
{
lean_object* v___x_2826_; 
lean_del_object(v___x_2823_);
lean_dec(v_stop_2821_);
lean_dec(v_start_2820_);
lean_dec_ref(v_array_2819_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v_b_2817_);
return v___x_2826_;
}
else
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2827_ = lean_unsigned_to_nat(0u);
v___x_2828_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__0));
v___x_2829_ = lean_array_fget_borrowed(v_array_2819_, v_start_2820_);
v___x_2830_ = lean_box(0);
v___x_2831_ = l_String_splitOnAux(v___x_2829_, v___x_2828_, v___x_2827_, v___x_2827_, v___x_2827_, v___x_2830_);
v___x_2832_ = lean_array_mk(v___x_2831_);
v___x_2833_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__1));
v___x_2834_ = l_Array_ithVal(v___x_2832_, v___x_2827_, v___x_2833_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; 
lean_dec_ref_known(v___x_2834_, 1);
v___x_2835_ = lean_unsigned_to_nat(1u);
v___x_2836_ = lean_array_get_size(v___x_2832_);
v___x_2837_ = lean_nat_sub(v___x_2836_, v___x_2835_);
v___x_2838_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__2));
v___x_2839_ = l_Array_ithVal(v___x_2832_, v___x_2837_, v___x_2838_);
lean_dec(v___x_2837_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v___x_2841_; lean_object* v___x_2843_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
v___x_2841_ = lean_nat_add(v_start_2820_, v___x_2835_);
lean_dec(v_start_2820_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 1, v___x_2841_);
v___x_2843_ = v___x_2823_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_array_2819_);
lean_ctor_set(v_reuseFailAlloc_2892_, 1, v___x_2841_);
lean_ctor_set(v_reuseFailAlloc_2892_, 2, v_stop_2821_);
v___x_2843_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
lean_object* v___x_2844_; uint8_t v___x_2845_; 
v___x_2844_ = lean_obj_once(&l_Int_roundedDiv___closed__0, &l_Int_roundedDiv___closed__0_once, _init_l_Int_roundedDiv___closed__0);
v___x_2845_ = lean_int_dec_eq(v_a_2840_, v___x_2844_);
lean_dec(v_a_2840_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; lean_object* v___x_2847_; 
lean_dec_ref(v___x_2832_);
v___x_2846_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__3));
v___x_2847_ = l_error___redArg(v___x_2846_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_dec_ref_known(v___x_2847_, 1);
v_a_2816_ = v___x_2843_;
goto _start;
}
else
{
lean_object* v_a_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2856_; 
lean_dec_ref(v___x_2843_);
lean_dec_ref(v_b_2817_);
v_a_2849_ = lean_ctor_get(v___x_2847_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2851_ = v___x_2847_;
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_a_2849_);
lean_dec(v___x_2847_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2856_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2854_; 
if (v_isShared_2852_ == 0)
{
v___x_2854_ = v___x_2851_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_a_2849_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
}
else
{
lean_object* v___x_2857_; lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2857_ = lean_unsigned_to_nat(2u);
v___x_2858_ = lean_nat_sub(v___x_2836_, v___x_2857_);
v___x_2859_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__4));
v___x_2860_ = l_Array_ithVal(v___x_2832_, v___x_2858_, v___x_2859_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = lean_obj_once(&l_instInhabitedEquation_default___closed__1, &l_instInhabitedEquation_default___closed__1_once, _init_l_instInhabitedEquation_default___closed__1);
v___x_2863_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__5));
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2863_);
lean_ctor_set(v___x_2864_, 1, v___x_2858_);
v___x_2865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2827_);
lean_ctor_set(v___x_2865_, 1, v___x_2835_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
v___x_2866_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg(v___x_2832_, v___x_2865_, v___x_2862_);
lean_dec_ref(v___x_2832_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v_size_2868_; uint8_t v___x_2869_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref_known(v___x_2866_, 1);
v_size_2868_ = lean_ctor_get(v_a_2867_, 0);
v___x_2869_ = lean_nat_dec_eq(v_size_2868_, v___x_2827_);
if (v___x_2869_ == 0)
{
if (v___x_2845_ == 0)
{
lean_dec(v_a_2867_);
lean_dec(v_a_2861_);
v_a_2816_ = v___x_2843_;
goto _start;
}
else
{
lean_object* v_size_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; 
v_size_2871_ = lean_ctor_get(v_b_2817_, 0);
lean_inc_n(v_size_2871_, 2);
v___x_2872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2872_, 0, v_size_2871_);
lean_ctor_set(v___x_2872_, 1, v_a_2867_);
lean_ctor_set(v___x_2872_, 2, v_a_2861_);
v___x_2873_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Std_HashMap_mapVals___at___00gcd_spec__0_spec__0___redArg(v_b_2817_, v_size_2871_, v___x_2872_);
v_a_2816_ = v___x_2843_;
v_b_2817_ = v___x_2873_;
goto _start;
}
}
else
{
lean_dec(v_a_2867_);
lean_dec(v_a_2861_);
v_a_2816_ = v___x_2843_;
goto _start;
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec(v_a_2861_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v_b_2817_);
v_a_2876_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2866_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2866_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v___x_2858_);
lean_dec_ref(v___x_2843_);
lean_dec_ref(v___x_2832_);
lean_dec_ref(v_b_2817_);
v_a_2884_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2860_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2860_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec_ref(v___x_2832_);
lean_del_object(v___x_2823_);
lean_dec(v_stop_2821_);
lean_dec(v_start_2820_);
lean_dec_ref(v_array_2819_);
lean_dec_ref(v_b_2817_);
v_a_2893_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2839_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2839_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___x_2832_);
lean_del_object(v___x_2823_);
lean_dec(v_stop_2821_);
lean_dec(v_start_2820_);
lean_dec_ref(v_array_2819_);
lean_dec_ref(v_b_2817_);
v_a_2901_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2834_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2834_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___boxed(lean_object* v_a_2910_, lean_object* v_b_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg(v_a_2910_, v_b_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(lean_object* v_s_2914_){
_start:
{
lean_object* v___x_2916_; lean_object* v_putStr_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_get_stdout();
v_putStr_2917_ = lean_ctor_get(v___x_2916_, 4);
lean_inc_ref(v_putStr_2917_);
lean_dec_ref(v___x_2916_);
v___x_2918_ = lean_apply_2(v_putStr_2917_, v_s_2914_, lean_box(0));
return v___x_2918_;
}
}
LEAN_EXPORT lean_object* l_IO_print___at___00IO_println___at___00main_spec__1_spec__1___boxed(lean_object* v_s_2919_, lean_object* v_a_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v_s_2919_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__1(lean_object* v_s_2922_){
_start:
{
uint32_t v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = 10;
v___x_2925_ = lean_string_push(v_s_2922_, v___x_2924_);
v___x_2926_ = l_IO_print___at___00IO_println___at___00main_spec__1_spec__1(v___x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l_IO_println___at___00main_spec__1___boxed(lean_object* v_s_2927_, lean_object* v_a_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_IO_println___at___00main_spec__1(v_s_2927_);
return v_res_2929_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00main_spec__5(lean_object* v_a_2930_, lean_object* v_a_2931_){
_start:
{
if (lean_obj_tag(v_a_2930_) == 0)
{
lean_object* v___x_2932_; 
v___x_2932_ = l_List_reverse___redArg(v_a_2931_);
return v___x_2932_;
}
else
{
lean_object* v_head_2933_; lean_object* v_tail_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2943_; 
v_head_2933_ = lean_ctor_get(v_a_2930_, 0);
v_tail_2934_ = lean_ctor_get(v_a_2930_, 1);
v_isSharedCheck_2943_ = !lean_is_exclusive(v_a_2930_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2936_ = v_a_2930_;
v_isShared_2937_ = v_isSharedCheck_2943_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_tail_2934_);
lean_inc(v_head_2933_);
lean_dec(v_a_2930_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2943_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
v___x_2938_ = l_Int_repr(v_head_2933_);
lean_dec(v_head_2933_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 1, v_a_2931_);
lean_ctor_set(v___x_2936_, 0, v___x_2938_);
v___x_2940_ = v___x_2936_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2938_);
lean_ctor_set(v_reuseFailAlloc_2942_, 1, v_a_2931_);
v___x_2940_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
v_a_2930_ = v_tail_2934_;
v_a_2931_ = v___x_2940_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_main___boxed__const__1(void){
_start:
{
uint32_t v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = 0;
v___x_2952_ = lean_box_uint32(v___x_2951_);
return v___x_2952_;
}
}
LEAN_EXPORT lean_object* _lean_main(lean_object* v_args_2953_){
_start:
{
lean_object* v___x_2958_; 
v___x_2958_ = l_List_head_x3f___redArg(v_args_2953_);
lean_dec(v_args_2953_);
if (lean_obj_tag(v___x_2958_) == 1)
{
lean_object* v_val_2959_; lean_object* v___f_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; 
v_val_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_val_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___f_2960_ = ((lean_object*)(l_main___closed__0));
v___x_2961_ = lean_alloc_closure((void*)(l_IO_FS_lines___boxed), 2, 1);
lean_closure_set(v___x_2961_, 0, v_val_2959_);
v___x_2962_ = l_Functor_mapRev___at___00main_spec__2___redArg(v___x_2961_, v___f_2960_);
if (lean_obj_tag(v___x_2962_) == 0)
{
lean_object* v_a_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v_a_2963_ = lean_ctor_get(v___x_2962_, 0);
lean_inc(v_a_2963_);
lean_dec_ref_known(v___x_2962_, 1);
v___x_2964_ = lean_unsigned_to_nat(0u);
v___x_2965_ = lean_array_get_size(v_a_2963_);
v___x_2966_ = lean_nat_dec_lt(v___x_2964_, v___x_2965_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; 
lean_dec(v_a_2963_);
v___x_2967_ = ((lean_object*)(l_main___closed__1));
v___x_2968_ = l_error___redArg(v___x_2967_);
return v___x_2968_;
}
else
{
lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; lean_object* v___x_2974_; lean_object* v___x_2975_; 
v___x_2969_ = lean_array_fget_borrowed(v_a_2963_, v___x_2964_);
v___x_2970_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg___closed__0));
v___x_2971_ = lean_box(0);
v___x_2972_ = l_String_splitOnAux(v___x_2969_, v___x_2970_, v___x_2964_, v___x_2964_, v___x_2964_, v___x_2971_);
v___x_2973_ = lean_array_mk(v___x_2972_);
v___x_2974_ = ((lean_object*)(l_main___closed__2));
v___x_2975_ = l_Array_ithVal(v___x_2973_, v___x_2964_, v___x_2974_);
if (lean_obj_tag(v___x_2975_) == 0)
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
lean_dec_ref_known(v___x_2975_, 1);
v___x_2976_ = lean_unsigned_to_nat(1u);
v___x_2977_ = ((lean_object*)(l_main___closed__3));
v___x_2978_ = l_Array_ithVal(v___x_2973_, v___x_2976_, v___x_2977_);
lean_dec_ref(v___x_2973_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = lean_obj_once(&l_instInhabitedEquation_default___closed__1, &l_instInhabitedEquation_default___closed__1_once, _init_l_instInhabitedEquation_default___closed__1);
v___x_2981_ = l_Array_toSubarray___redArg(v_a_2963_, v___x_2976_, v___x_2965_);
v___x_2982_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg(v___x_2981_, v___x_2980_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2995_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2995_ = l_preprocess_x3f(v_a_2983_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec(v_a_2979_);
goto v___jp_2984_;
}
else
{
lean_object* v_val_2996_; lean_object* v_size_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_val_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v_size_2997_ = lean_ctor_get(v_val_2996_, 0);
lean_inc(v_size_2997_);
v___x_2998_ = lean_nat_abs(v_a_2979_);
lean_dec(v_a_2979_);
v___x_2999_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2999_, 0, v_val_2996_);
lean_ctor_set(v___x_2999_, 1, v___x_2980_);
lean_ctor_set(v___x_2999_, 2, v_size_2997_);
lean_ctor_set(v___x_2999_, 3, v___x_2998_);
v___x_3000_ = l_solveProblem(v___x_2999_);
if (lean_obj_tag(v___x_3000_) == 0)
{
goto v___jp_2984_;
}
else
{
lean_object* v_assignment_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; 
v_assignment_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc_ref(v_assignment_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = ((lean_object*)(l_main___closed__5));
v___x_3003_ = l_IO_println___at___00main_spec__1(v___x_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
lean_dec_ref_known(v___x_3003_, 1);
v___x_3004_ = lean_array_to_list(v_assignment_3001_);
v___x_3005_ = l_List_mapTR_loop___at___00main_spec__5(v___x_3004_, v___x_2971_);
v___x_3006_ = l_String_intercalate(v___x_2970_, v___x_3005_);
v___x_3007_ = l_IO_println___at___00main_spec__1(v___x_3006_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_dec_ref_known(v___x_3007_, 1);
goto v___jp_2955_;
}
else
{
lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_assignment_3001_);
v_a_3016_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3003_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3003_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
}
v___jp_2984_:
{
lean_object* v___x_2985_; lean_object* v___x_2986_; 
v___x_2985_ = ((lean_object*)(l_main___closed__4));
v___x_2986_ = l_IO_println___at___00main_spec__1(v___x_2985_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_dec_ref_known(v___x_2986_, 1);
goto v___jp_2955_;
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
lean_dec(v_a_2979_);
v_a_3024_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3031_ == 0)
{
v___x_3026_ = v___x_2982_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_2982_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec(v_a_2963_);
v_a_3032_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_2978_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_2978_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v___x_2973_);
lean_dec(v_a_2963_);
v_a_3040_ = lean_ctor_get(v___x_2975_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2975_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2975_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
v_a_3048_ = lean_ctor_get(v___x_2962_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2962_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2962_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2962_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
lean_dec(v___x_2958_);
v___x_3056_ = ((lean_object*)(l_main___closed__6));
v___x_3057_ = l_error___redArg(v___x_3056_);
return v___x_3057_;
}
v___jp_2955_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2956_ = l_main___boxed__const__1;
v___x_2957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2957_, 0, v___x_2956_);
return v___x_2957_;
}
}
}
LEAN_EXPORT lean_object* l_main___boxed(lean_object* v_args_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = _lean_main(v_args_3058_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3(lean_object* v___x_3061_, lean_object* v_inst_3062_, lean_object* v_R_3063_, lean_object* v_a_3064_, lean_object* v_b_3065_, lean_object* v_c_3066_){
_start:
{
lean_object* v___x_3068_; 
v___x_3068_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__3___redArg(v___x_3061_, v_a_3064_, v_b_3065_);
return v___x_3068_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__3___boxed(lean_object* v___x_3069_, lean_object* v_inst_3070_, lean_object* v_R_3071_, lean_object* v_a_3072_, lean_object* v_b_3073_, lean_object* v_c_3074_, lean_object* v___y_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__3(v___x_3069_, v_inst_3070_, v_R_3071_, v_a_3072_, v_b_3073_, v_c_3074_);
lean_dec_ref(v___x_3069_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4(lean_object* v_inst_3077_, lean_object* v_R_3078_, lean_object* v_a_3079_, lean_object* v_b_3080_, lean_object* v_c_3081_){
_start:
{
lean_object* v___x_3083_; 
v___x_3083_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__4___redArg(v_a_3079_, v_b_3080_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00main_spec__4___boxed(lean_object* v_inst_3084_, lean_object* v_R_3085_, lean_object* v_a_3086_, lean_object* v_b_3087_, lean_object* v_c_3088_, lean_object* v___y_3089_){
_start:
{
lean_object* v_res_3090_; 
v_res_3090_ = l_WellFounded_opaqueFix_u2083___at___00main_spec__4(v_inst_3084_, v_R_3085_, v_a_3086_, v_b_3087_, v_c_3088_);
return v_res_3090_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Producers_Range(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Combinators_StepSize(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_liasolver(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_AssocList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Producers_Range(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Combinators_StepSize(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_instInhabitedEquation_default = _init_l_instInhabitedEquation_default();
lean_mark_persistent(l_instInhabitedEquation_default);
l_instInhabitedEquation = _init_l_instInhabitedEquation();
lean_mark_persistent(l_instInhabitedEquation);
l_instInhabitedProblem_default = _init_l_instInhabitedProblem_default();
lean_mark_persistent(l_instInhabitedProblem_default);
l_instInhabitedProblem = _init_l_instInhabitedProblem();
lean_mark_persistent(l_instInhabitedProblem);
l_instInhabitedSolution_default = _init_l_instInhabitedSolution_default();
lean_mark_persistent(l_instInhabitedSolution_default);
l_instInhabitedSolution = _init_l_instInhabitedSolution();
lean_mark_persistent(l_instInhabitedSolution);
l_main___boxed__const__1 = _init_l_main___boxed__const__1();
lean_mark_persistent(l_main___boxed__const__1);
return lean_io_result_mk_ok(lean_box(0));
}
char ** lean_setup_args(int argc, char ** argv);
void lean_initialize();
#if defined(WIN32) || defined(_WIN32)
#include <windows.h>
#endif
lean_object* run_main(int argc, char ** argv) {
    lean_object* in = lean_box(0);
    int i = argc;
    while (i > 1) {
      lean_object* n;
      i--;
      n = lean_alloc_ctor(1,2,0); lean_ctor_set(n, 0, lean_mk_string(argv[i])); lean_ctor_set(n, 1, in);
      in = n;
    }
    return _lean_main(in);
}
int main(int argc, char ** argv) {
#if defined(WIN32) || defined(_WIN32)
  SetErrorMode(SEM_FAILCRITICALERRORS);
  SetConsoleOutputCP(CP_UTF8);
#endif
  lean_object* res;
  argv = lean_setup_args(argc, argv);
  lean_initialize();
  res = initialize_liasolver(1 /* builtin */);
  lean_io_mark_end_initialization();
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
    lean_init_task_manager();
    res = lean_run_main(&run_main, argc, argv);
  }
  lean_finalize_task_manager();
  if (lean_io_result_is_ok(res)) {
    int ret = lean_unbox_uint32(lean_io_result_get_value(res));
    lean_dec_ref(res);
    return ret;
  } else {
    lean_io_result_show_error(res);
    lean_dec_ref(res);
    return 1;
  }
}
#ifdef __cplusplus
}
#endif
