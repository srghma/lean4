// Lean compiler output
// Module: Lean.Kernel.Inductive.Add
// Imports: public import Lean.Environment public import Lean.Kernel.TypeChecker
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
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Except_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_pure(lean_object*, lean_object*, lean_object*);
lean_object* l_Except_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Except_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_instMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
uint64_t lean_usize_to_uint64(size_t);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Environment_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
uint8_t l_Lean_Kernel_Environment_contains(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev_range(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_whnf___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_M_run___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_consume_type_annotations(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_inferType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLambda(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedInductiveType_default;
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
lean_object* l_Lean_mkRecName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_LocalContext_get_x21(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Environment_checkNoMVarNoFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_checkType___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* l_Lean_Kernel_TypeChecker_ensureType___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isZero(lean_object*);
lean_object* l_Lean_Expr_sortLevel_x21(lean_object*);
uint8_t l_Lean_Level_geq_x27(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_isDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedConstructor_default;
uint8_t l_Lean_Level_isParam(lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_getEnv___boxed(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Kernel_Environment_checkName(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_inferImplicit(lean_object*, lean_object*, uint8_t);
lean_object* lean_environment_add(lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_bind___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkPtrMap___redArg(lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_ensureSort___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isEquiv_x27(lean_object*, lean_object*);
uint8_t l_Lean_Level_isNeverZero(lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
lean_object* l_ReaderT_read___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_drop___redArg(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Kernel_Environment_checkDuplicatedUnivParams(lean_object*);
static const lean_string_object l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__0_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__1_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__2;
static const lean_array_object l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__3 = (const lean_object*)&l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__3_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__4;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instInhabitedRecInfo_default;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instInhabitedRecInfo;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__0;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__1;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__2;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__3;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4;
static const lean_array_object l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__5 = (const lean_object*)&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__5_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__6;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instInhabitedInductiveStats;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLiftMM___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLiftMM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean4Lean_AddInductive_instMonadLiftMM___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLiftMM___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLiftMM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_AddInductive_instMonadLiftMM = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLiftMM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___lam__0___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean4Lean_AddInductive_instMonadLCtxM___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__0_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__1_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__1, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__2_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__2___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__3 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__3_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__4 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__4_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_map, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__5 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__5_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__5_value),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__1_value)}};
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__6 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__6_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_pure, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__7 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__7_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__6_value),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__7_value),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__2_value),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__3_value),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__4_value)}};
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__8 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__8_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Except_bind, .m_arity = 5, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__9 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__9_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__8_value),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__9_value)}};
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_read___boxed, .m_arity = 4, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__11 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__11_value;
static const lean_closure_object l_Lean4Lean_AddInductive_instMonadLCtxM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind___boxed, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__11_value),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__0_value)} };
static const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___closed__12 = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__12_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM = (const lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__12_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getType(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getType___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__0_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "parameters of all inductive datatypes must match"};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__1_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__1_value)}};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__2_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__2_value)}};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__3 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__3_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "number of parameters mismatch in inductive datatype declaration"};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__4 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__4_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__4_value)}};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__5 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__5_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__5_value)}};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__6 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__6_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_AddInductive_checkInductiveTypes_loopInd_spec__0(lean_object*);
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 56, .m_capacity = 56, .m_length = 55, .m_data = "mutually inductive types must live in the same universe"};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__0_value)}};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__1_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__1_value)}};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__2_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 141, .m_capacity = 141, .m_length = 140, .m_data = "assertion violation: stats.levels.length == ( __do_lift._@.Lean.Kernel.Inductive.Add.2156216642._hygCtx._hyg.138.0 ).lparams.length\n        "};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__2_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Lean4Lean.AddInductive.checkInductiveTypes.loopInd"};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__1_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Kernel.Inductive.Add"};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__3;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "assertion violation: stats.nindices.size == indTypes.size\n        "};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__4 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__4_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__5;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "assertion violation: stats.indConsts.size == indTypes.size\n        "};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__6 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__6_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__7;
static const lean_string_object l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 59, .m_capacity = 59, .m_length = 58, .m_data = "assertion violation: stats.params.size == nparams\n        "};
static const lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__8 = (const lean_object*)&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__8_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__9;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean4Lean_AddInductive_checkInductiveTypes_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_hasIndOcc_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_hasIndOcc_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_hasIndOcc___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_hasIndOcc___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_hasIndOcc(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_hasIndOcc___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isRec_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRec_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean4Lean_AddInductive_isRec_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean4Lean_AddInductive_isRec_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isRec_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isRec_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isRec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRec___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isReflexive_loop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isReflexive_loop___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_any___at___00Lean4Lean_AddInductive_isReflexive_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_any___at___00Lean4Lean_AddInductive_isReflexive_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isReflexive_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isReflexive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isReflexive(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isReflexive___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean4Lean_AddInductive_declareInductiveTypes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_AddInductive_declareInductiveTypes___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_declareInductiveTypes___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareInductiveTypes(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareInductiveTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__1 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__1_value;
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__2_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0;
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isValidIndAppIdx(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isValidIndAppIdx___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isValidIndApp_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean4Lean_AddInductive_isRecArg_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_isRecArg_loop___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_isRecArg_loop___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRecArg_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRecArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRecArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean4Lean_AddInductive_checkPositivity_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_checkPositivity_loop___closed__0_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_checkPositivity_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_checkPositivity_loop___closed__1_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkPositivity_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arg #"};
static const lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_checkPositivity_loop___closed__2_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkPositivity_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " of '"};
static const lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___closed__3 = (const lean_object*)&l_Lean4Lean_AddInductive_checkPositivity_loop___closed__3_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkPositivity_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "' has a non positive occurrence of the datatypes being declared"};
static const lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___closed__4 = (const lean_object*)&l_Lean4Lean_AddInductive_checkPositivity_loop___closed__4_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkPositivity_loop___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "' has a non valid occurrence of the datatypes being declared"};
static const lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___closed__5 = (const lean_object*)&l_Lean4Lean_AddInductive_checkPositivity_loop___closed__5_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_AddInductive_checkConstructors_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "universe level of type_of(arg #"};
static const lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_checkConstructors_loop___closed__0_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkConstructors_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = ") of '"};
static const lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_checkConstructors_loop___closed__1_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkConstructors_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "' is too big for the corresponding inductive datatype"};
static const lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_checkConstructors_loop___closed__2_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkConstructors_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "' does not match inductive datatype parameters"};
static const lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___closed__3 = (const lean_object*)&l_Lean4Lean_AddInductive_checkConstructors_loop___closed__3_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkConstructors_loop___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "invalid return type for '"};
static const lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___closed__4 = (const lean_object*)&l_Lean4Lean_AddInductive_checkConstructors_loop___closed__4_value;
static const lean_string_object l_Lean4Lean_AddInductive_checkConstructors_loop___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___closed__5 = (const lean_object*)&l_Lean4Lean_AddInductive_checkConstructors_loop___closed__5_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "duplicate constructor name '"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors_arity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors_arity___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_AddInductive_declareConstructors_spec__0(lean_object*);
static const lean_string_object l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "Lean4Lean.AddInductive.declareConstructors"};
static const lean_object* l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__0 = (const lean_object*)&l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__0_value;
static const lean_string_object l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 46, .m_data = "assertion violation: arity ≥ stats.params.size"};
static const lean_object* l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__1 = (const lean_object*)&l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__1_value;
static lean_once_cell_t l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__2;
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareConstructors_spec__2(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareConstructors_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__1(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(15) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__0_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__1_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean4Lean_AddInductive_isLargeEliminator___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_AddInductive_isLargeEliminator___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_isLargeEliminator___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00Lean4Lean_AddInductive_getElimLevel_loop_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00Lean4Lean_AddInductive_getElimLevel_loop_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_AddInductive_getElimLevel_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l_Lean4Lean_AddInductive_getElimLevel_loop___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_getElimLevel_loop___closed__0_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_getElimLevel_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_getElimLevel_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l_Lean4Lean_AddInductive_getElimLevel_loop___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_getElimLevel_loop___closed__1_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel_loop___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean4Lean_AddInductive_getElimLevel___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_getElimLevel___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_getElimLevel___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isKTarget_loop(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget_loop___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean4Lean_AddInductive_isKTarget___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean4Lean_AddInductive_isKTarget___redArg___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_isKTarget___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_AddInductive_getIIndices___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Init.Data.Option.BasicAux"};
static const lean_object* l_Lean4Lean_AddInductive_getIIndices___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_getIIndices___closed__0_value;
static const lean_string_object l_Lean4Lean_AddInductive_getIIndices___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Option.get!"};
static const lean_object* l_Lean4Lean_AddInductive_getIIndices___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_getIIndices___closed__1_value;
static const lean_string_object l_Lean4Lean_AddInductive_getIIndices___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "value is none"};
static const lean_object* l_Lean4Lean_AddInductive_getIIndices___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_getIIndices___closed__2_value;
static lean_once_cell_t l_Lean4Lean_AddInductive_getIIndices___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_AddInductive_getIIndices___closed__3;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getIIndices(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "t"};
static const lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(123, 228, 43, 115, 146, 126, 91, 53)}};
static const lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__1 = (const lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__1_value;
static const lean_string_object l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "motive"};
static const lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__2_value;
static const lean_ctor_object l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(129, 10, 150, 230, 97, 79, 179, 234)}};
static const lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__3 = (const lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__3_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_ih"};
static const lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Inductive_Add_0__Lean4Lean_AddInductive_mkRecInfos_loopU_match__1_splitter___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Inductive_Add_0__Lean4Lean_AddInductive_mkRecInfos_loopU_match__1_splitter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean4Lean_AddInductive_mkRecInfos___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_mkRecInfos___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getRecLevels(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getRecLevelParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getRecLevelParams___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean4Lean_AddInductive_mkRecRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_AddInductive_mkRecRules___closed__0 = (const lean_object*)&l_Lean4Lean_AddInductive_mkRecRules___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_run_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_run_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___redArg___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_run_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_run_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_getNestedIfAuxCtor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_getNestedIfAuxCtor___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0(lean_object*);
static lean_once_cell_t l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1(lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "Lean4Lean.ElimNestedInductive.Result.restoreCtorName"};
static const lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__0_value;
static const lean_string_object l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1_value;
static lean_once_cell_t l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__2;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__3(lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "Lean4Lean.ElimNestedInductive.Result.restoreNested"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__1;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 52, .m_capacity = 52, .m_length = 49, .m_data = "assertion violation: args.size ≥ r.nparams\n      "};
static const lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__0_value;
static lean_once_cell_t l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__1;
static const lean_string_object l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 47, .m_data = "assertion violation: args.size ≥ r.nparams\n    "};
static const lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__2 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__2_value;
static lean_once_cell_t l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__0;
static const lean_string_object l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "_nested_fresh"};
static const lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__1_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__1_value),LEAN_SCALAR_PTR_LITERAL(28, 54, 255, 134, 23, 229, 169, 43)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__2 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__2_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__3 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__3_value;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__0_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__3_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_ElimNestedInductive_instInhabitedState_default = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_ElimNestedInductive_instInhabitedState = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__0_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__1___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__1_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__2___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__2 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__2_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__1, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__3 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__3_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__4, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__4 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__4_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__7, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__5 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__5_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_instMonad___redArg___lam__9, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__6 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__6_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_map, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__7 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__7_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__7_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__3_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__8 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__8_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_pure, .m_arity = 6, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__9 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__9_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__8_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__9_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__4_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__5_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__6_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__10 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__10_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateT_bind, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_AddInductive_instMonadLCtxM___closed__10_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__11 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__11_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__10_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__11_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12_value;
static const lean_closure_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*7, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_ReaderT_bind___boxed, .m_arity = 8, .m_num_fixed = 7, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__0_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__1_value)} };
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__13 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__13_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__13_value),((lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__2_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__14 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__14_value;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_illFormed___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "invalid nested inductive datatype, ill-formed declaration"};
static const lean_object* l_Lean4Lean_ElimNestedInductive_illFormed___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_illFormed___closed__0_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_illFormed___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_illFormed___closed__0_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_illFormed___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_illFormed___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean4Lean_ElimNestedInductive_illFormed = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_illFormed___closed__1_value;
static lean_once_cell_t l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_replaceParams___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 44, .m_capacity = 44, .m_length = 43, .m_data = "Lean4Lean.ElimNestedInductive.replaceParams"};
static const lean_object* l_Lean4Lean_ElimNestedInductive_replaceParams___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_replaceParams___closed__0_value;
static const lean_string_object l_Lean4Lean_ElimNestedInductive_replaceParams___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "assertion violation: As.size == params.size\n  "};
static const lean_object* l_Lean4Lean_ElimNestedInductive_replaceParams___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_replaceParams___closed__1_value;
static lean_once_cell_t l_Lean4Lean_ElimNestedInductive_replaceParams___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_ElimNestedInductive_replaceParams___closed__2;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___lam__0(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 119, .m_capacity = 119, .m_length = 118, .m_data = "invalid nested inductive datatype '{fn\n      }', nested inductive datatypes parameters cannot contain local variables."};
static const lean_object* l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__0_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__0_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__1_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__1_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__2 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__2_value;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_illFormed___closed__1_value)}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instantiateForallParams(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instantiateForallParams___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_nested"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 235, 124, 147, 33, 31, 161, 8)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__1_value;
static const lean_string_object l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "Lean4Lean.ElimNestedInductive.replaceIfNested"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__2_value;
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 45, .m_data = "assertion violation: I_nparams ≤ args.size\n  "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__0_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__1;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "assertion violation: result.isSome\n  "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__2_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__3;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__4;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceIfNested(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceIfNested___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean4Lean_ElimNestedInductive_replaceAllNested___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_ElimNestedInductive_replaceAllNested___closed__0;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceAllNested(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceAllNested___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "invalid inductive datatype declaration, incorrect number of parameters"};
static const lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__0_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__0_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__1_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__1_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__2 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "Lean4Lean.ElimNestedInductive.run.loop"};
static const lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__0 = (const lean_object*)&l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__0_value;
static const lean_string_object l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: As.size == nparams\n        "};
static const lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__1 = (const lean_object*)&l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__1_value;
static lean_once_cell_t l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__2;
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_run_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "deep recursion: ElimNestedInductive.run.loop"};
static const lean_object* l_Lean4Lean_ElimNestedInductive_run_loop___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_run_loop___closed__0_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_run_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_run_loop___closed__0_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_run_loop___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_run_loop___closed__1_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_run_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_run_loop___closed__1_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_run_loop___closed__2 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_run_loop___closed__2_value;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_ElimNestedInductive_run___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 100, .m_capacity = 100, .m_length = 99, .m_data = "invalid empty (mutual) inductive datatype declaration, it must contain at least one inductive type."};
static const lean_object* l_Lean4Lean_ElimNestedInductive_run___closed__0 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_run___closed__0_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_run___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_run___closed__0_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_run___closed__1 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_run___closed__1_value;
static const lean_ctor_object l_Lean4Lean_ElimNestedInductive_run___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_ElimNestedInductive_run___closed__1_value)}};
static const lean_object* l_Lean4Lean_ElimNestedInductive_run___closed__2 = (const lean_object*)&l_Lean4Lean_ElimNestedInductive_run___closed__2_value;
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_mkAuxRecNameMap___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean4Lean.mkAuxRecNameMap"};
static const lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__0 = (const lean_object*)&l_Lean4Lean_mkAuxRecNameMap___closed__0_value;
static lean_once_cell_t l_Lean4Lean_mkAuxRecNameMap___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__1;
static const lean_string_object l_Lean4Lean_mkAuxRecNameMap___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "assertion violation: allNames.length > ntypes\n  "};
static const lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__2 = (const lean_object*)&l_Lean4Lean_mkAuxRecNameMap___closed__2_value;
static lean_once_cell_t l_Lean4Lean_mkAuxRecNameMap___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__3;
static const lean_array_object l_Lean4Lean_mkAuxRecNameMap___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__4 = (const lean_object*)&l_Lean4Lean_mkAuxRecNameMap___closed__4_value;
static const lean_ctor_object l_Lean4Lean_mkAuxRecNameMap___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__5 = (const lean_object*)&l_Lean4Lean_mkAuxRecNameMap___closed__5_value;
static const lean_ctor_object l_Lean4Lean_mkAuxRecNameMap___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_mkAuxRecNameMap___closed__4_value),((lean_object*)&l_Lean4Lean_mkAuxRecNameMap___closed__5_value)}};
static const lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__6 = (const lean_object*)&l_Lean4Lean_mkAuxRecNameMap___closed__6_value;
static lean_once_cell_t l_Lean4Lean_mkAuxRecNameMap___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_mkAuxRecNameMap___closed__7;
LEAN_EXPORT lean_object* l_Lean4Lean_mkAuxRecNameMap(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean4Lean_Environment_addInductive_spec__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean4Lean_Environment_addInductive_spec__1___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean4Lean.Environment.addInductive"};
static const lean_object* l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__0 = (const lean_object*)&l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__0_value;
static lean_once_cell_t l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1;
LEAN_EXPORT lean_object* l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean4Lean_Environment_addInductive_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean4Lean_Environment_addInductive_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean4Lean_Environment_addInductive_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_Environment_addInductive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "_ind_fresh"};
static const lean_object* l_Lean4Lean_Environment_addInductive___closed__0 = (const lean_object*)&l_Lean4Lean_Environment_addInductive___closed__0_value;
static const lean_ctor_object l_Lean4Lean_Environment_addInductive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean4Lean_Environment_addInductive___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 90, 226, 88, 57, 75, 187, 150)}};
static const lean_object* l_Lean4Lean_Environment_addInductive___closed__1 = (const lean_object*)&l_Lean4Lean_Environment_addInductive___closed__1_value;
static const lean_ctor_object l_Lean4Lean_Environment_addInductive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_Environment_addInductive___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean4Lean_Environment_addInductive___closed__2 = (const lean_object*)&l_Lean4Lean_Environment_addInductive___closed__2_value;
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_addInductive(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_addInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_box(0);
v___x_5_ = ((lean_object*)(l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__1));
v___x_6_ = l_Lean_Expr_const___override(v___x_5_, v___x_4_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__4(void){
_start:
{
lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v___x_9_ = ((lean_object*)(l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__3));
v___x_10_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__2, &l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__2_once, _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__2);
v___x_11_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_11_, 0, v___x_10_);
lean_ctor_set(v___x_11_, 1, v___x_9_);
lean_ctor_set(v___x_11_, 2, v___x_9_);
lean_ctor_set(v___x_11_, 3, v___x_10_);
return v___x_11_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo_default(void){
_start:
{
lean_object* v___x_12_; 
v___x_12_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__4, &l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__4_once, _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__4);
return v___x_12_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo(void){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean4Lean_AddInductive_instInhabitedRecInfo_default;
return v___x_13_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__0(void){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_14_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__1(void){
_start:
{
lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_15_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__0, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__0_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__0);
v___x_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__2(void){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_17_ = lean_unsigned_to_nat(32u);
v___x_18_ = lean_mk_empty_array_with_capacity(v___x_17_);
v___x_19_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_19_, 0, v___x_18_);
return v___x_19_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__3(void){
_start:
{
size_t v___x_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_20_ = ((size_t)5ULL);
v___x_21_ = lean_unsigned_to_nat(0u);
v___x_22_ = lean_unsigned_to_nat(32u);
v___x_23_ = lean_mk_empty_array_with_capacity(v___x_22_);
v___x_24_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__2, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__2_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__2);
v___x_25_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v___x_23_);
lean_ctor_set(v___x_25_, 2, v___x_21_);
lean_ctor_set(v___x_25_, 3, v___x_21_);
lean_ctor_set_usize(v___x_25_, 4, v___x_20_);
return v___x_25_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4(void){
_start:
{
lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_26_ = lean_box(1);
v___x_27_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__3, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__3_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__3);
v___x_28_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__1, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__1_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__1);
v___x_29_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_27_);
lean_ctor_set(v___x_29_, 2, v___x_26_);
return v___x_29_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__6(void){
_start:
{
uint8_t v___x_32_; lean_object* v___x_33_; lean_object* v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; lean_object* v___x_37_; lean_object* v___x_38_; 
v___x_32_ = 0;
v___x_33_ = ((lean_object*)(l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__3));
v___x_34_ = ((lean_object*)(l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__5));
v___x_35_ = lean_box(0);
v___x_36_ = lean_box(0);
v___x_37_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4);
v___x_38_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_38_, 0, v___x_37_);
lean_ctor_set(v___x_38_, 1, v___x_36_);
lean_ctor_set(v___x_38_, 2, v___x_35_);
lean_ctor_set(v___x_38_, 3, v___x_34_);
lean_ctor_set(v___x_38_, 4, v___x_33_);
lean_ctor_set(v___x_38_, 5, v___x_33_);
lean_ctor_set_uint8(v___x_38_, sizeof(void*)*6, v___x_32_);
return v___x_38_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default(void){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__6, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__6_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__6);
return v___x_39_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats(void){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default;
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLocalNameGeneratorM___lam__0(lean_object* v_00_u03b1_41_, lean_object* v_f_42_, lean_object* v_c_43_){
_start:
{
lean_object* v_ngen_44_; lean_object* v_env_45_; lean_object* v_lctx_46_; lean_object* v_lparams_47_; uint8_t v_safety_48_; uint8_t v_allowPrimitive_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_69_; 
v_ngen_44_ = lean_ctor_get(v_c_43_, 3);
v_env_45_ = lean_ctor_get(v_c_43_, 0);
v_lctx_46_ = lean_ctor_get(v_c_43_, 1);
v_lparams_47_ = lean_ctor_get(v_c_43_, 2);
v_safety_48_ = lean_ctor_get_uint8(v_c_43_, sizeof(void*)*4);
v_allowPrimitive_49_ = lean_ctor_get_uint8(v_c_43_, sizeof(void*)*4 + 1);
v_isSharedCheck_69_ = !lean_is_exclusive(v_c_43_);
if (v_isSharedCheck_69_ == 0)
{
v___x_51_ = v_c_43_;
v_isShared_52_ = v_isSharedCheck_69_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_ngen_44_);
lean_inc(v_lparams_47_);
lean_inc(v_lctx_46_);
lean_inc(v_env_45_);
lean_dec(v_c_43_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_69_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v_namePrefix_53_; lean_object* v_idx_54_; lean_object* v___x_56_; uint8_t v_isShared_57_; uint8_t v_isSharedCheck_68_; 
v_namePrefix_53_ = lean_ctor_get(v_ngen_44_, 0);
v_idx_54_ = lean_ctor_get(v_ngen_44_, 1);
v_isSharedCheck_68_ = !lean_is_exclusive(v_ngen_44_);
if (v_isSharedCheck_68_ == 0)
{
v___x_56_ = v_ngen_44_;
v_isShared_57_ = v_isSharedCheck_68_;
goto v_resetjp_55_;
}
else
{
lean_inc(v_idx_54_);
lean_inc(v_namePrefix_53_);
lean_dec(v_ngen_44_);
v___x_56_ = lean_box(0);
v_isShared_57_ = v_isSharedCheck_68_;
goto v_resetjp_55_;
}
v_resetjp_55_:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
lean_inc(v_idx_54_);
lean_inc(v_namePrefix_53_);
v___x_58_ = l_Lean_Name_num___override(v_namePrefix_53_, v_idx_54_);
v___x_59_ = lean_unsigned_to_nat(1u);
v___x_60_ = lean_nat_add(v_idx_54_, v___x_59_);
lean_dec(v_idx_54_);
if (v_isShared_57_ == 0)
{
lean_ctor_set(v___x_56_, 1, v___x_60_);
v___x_62_ = v___x_56_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_67_; 
v_reuseFailAlloc_67_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_67_, 0, v_namePrefix_53_);
lean_ctor_set(v_reuseFailAlloc_67_, 1, v___x_60_);
v___x_62_ = v_reuseFailAlloc_67_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_64_; 
if (v_isShared_52_ == 0)
{
lean_ctor_set(v___x_51_, 3, v___x_62_);
v___x_64_ = v___x_51_;
goto v_reusejp_63_;
}
else
{
lean_object* v_reuseFailAlloc_66_; 
v_reuseFailAlloc_66_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v_reuseFailAlloc_66_, 0, v_env_45_);
lean_ctor_set(v_reuseFailAlloc_66_, 1, v_lctx_46_);
lean_ctor_set(v_reuseFailAlloc_66_, 2, v_lparams_47_);
lean_ctor_set(v_reuseFailAlloc_66_, 3, v___x_62_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, sizeof(void*)*4, v_safety_48_);
lean_ctor_set_uint8(v_reuseFailAlloc_66_, sizeof(void*)*4 + 1, v_allowPrimitive_49_);
v___x_64_ = v_reuseFailAlloc_66_;
goto v_reusejp_63_;
}
v_reusejp_63_:
{
lean_object* v___x_65_; 
v___x_65_ = lean_apply_2(v_f_42_, v___x_58_, v___x_64_);
return v___x_65_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLiftMM___lam__0(lean_object* v_00_u03b1_72_, lean_object* v_x_73_, lean_object* v_c_74_){
_start:
{
lean_object* v_env_75_; lean_object* v_lctx_76_; lean_object* v_lparams_77_; uint8_t v_safety_78_; lean_object* v___x_79_; 
v_env_75_ = lean_ctor_get(v_c_74_, 0);
lean_inc_ref(v_env_75_);
v_lctx_76_ = lean_ctor_get(v_c_74_, 1);
lean_inc_ref(v_lctx_76_);
v_lparams_77_ = lean_ctor_get(v_c_74_, 2);
lean_inc(v_lparams_77_);
v_safety_78_ = lean_ctor_get_uint8(v_c_74_, sizeof(void*)*4);
lean_dec_ref(v_c_74_);
v___x_79_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_75_, v_safety_78_, v_lctx_76_, v_lparams_77_, v_x_73_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___lam__0(lean_object* v_00_u03b1_82_, lean_object* v_f_83_, lean_object* v_x_84_, lean_object* v___y_85_){
_start:
{
lean_object* v_env_86_; lean_object* v_lctx_87_; lean_object* v_lparams_88_; lean_object* v_ngen_89_; uint8_t v_safety_90_; uint8_t v_allowPrimitive_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v_env_86_ = lean_ctor_get(v___y_85_, 0);
v_lctx_87_ = lean_ctor_get(v___y_85_, 1);
v_lparams_88_ = lean_ctor_get(v___y_85_, 2);
v_ngen_89_ = lean_ctor_get(v___y_85_, 3);
v_safety_90_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*4);
v_allowPrimitive_91_ = lean_ctor_get_uint8(v___y_85_, sizeof(void*)*4 + 1);
lean_inc_ref(v_lctx_87_);
v___x_92_ = lean_apply_1(v_f_83_, v_lctx_87_);
lean_inc_ref(v_ngen_89_);
lean_inc(v_lparams_88_);
lean_inc_ref(v_env_86_);
v___x_93_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_93_, 0, v_env_86_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
lean_ctor_set(v___x_93_, 2, v_lparams_88_);
lean_ctor_set(v___x_93_, 3, v_ngen_89_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*4, v_safety_90_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*4 + 1, v_allowPrimitive_91_);
v___x_94_ = lean_apply_1(v_x_84_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___lam__0___boxed(lean_object* v_00_u03b1_95_, lean_object* v_f_96_, lean_object* v_x_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean4Lean_AddInductive_instMonadWithReaderOfLocalContextM___lam__0(v_00_u03b1_95_, v_f_96_, v_x_97_, v___y_98_);
lean_dec_ref(v___y_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___lam__0(lean_object* v_____do__lift_102_, lean_object* v___y_103_){
_start:
{
lean_object* v_lctx_104_; lean_object* v___x_105_; 
v_lctx_104_ = lean_ctor_get(v_____do__lift_102_, 1);
lean_inc_ref(v_lctx_104_);
v___x_105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_105_, 0, v_lctx_104_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_instMonadLCtxM___lam__0___boxed(lean_object* v_____do__lift_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean4Lean_AddInductive_instMonadLCtxM___lam__0(v_____do__lift_106_, v___y_107_);
lean_dec_ref(v___y_107_);
lean_dec_ref(v_____do__lift_106_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv___redArg(lean_object* v_env_136_, lean_object* v_x_137_, lean_object* v_a_138_){
_start:
{
lean_object* v_lctx_139_; lean_object* v_lparams_140_; lean_object* v_ngen_141_; uint8_t v_safety_142_; uint8_t v_allowPrimitive_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_lctx_139_ = lean_ctor_get(v_a_138_, 1);
v_lparams_140_ = lean_ctor_get(v_a_138_, 2);
v_ngen_141_ = lean_ctor_get(v_a_138_, 3);
v_safety_142_ = lean_ctor_get_uint8(v_a_138_, sizeof(void*)*4);
v_allowPrimitive_143_ = lean_ctor_get_uint8(v_a_138_, sizeof(void*)*4 + 1);
lean_inc_ref(v_ngen_141_);
lean_inc(v_lparams_140_);
lean_inc_ref(v_lctx_139_);
v___x_144_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_144_, 0, v_env_136_);
lean_ctor_set(v___x_144_, 1, v_lctx_139_);
lean_ctor_set(v___x_144_, 2, v_lparams_140_);
lean_ctor_set(v___x_144_, 3, v_ngen_141_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*4, v_safety_142_);
lean_ctor_set_uint8(v___x_144_, sizeof(void*)*4 + 1, v_allowPrimitive_143_);
v___x_145_ = lean_apply_1(v_x_137_, v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv___redArg___boxed(lean_object* v_env_146_, lean_object* v_x_147_, lean_object* v_a_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Lean4Lean_AddInductive_withEnv___redArg(v_env_146_, v_x_147_, v_a_148_);
lean_dec_ref(v_a_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv(lean_object* v_00_u03b1_150_, lean_object* v_env_151_, lean_object* v_x_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_lctx_154_; lean_object* v_lparams_155_; lean_object* v_ngen_156_; uint8_t v_safety_157_; uint8_t v_allowPrimitive_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_lctx_154_ = lean_ctor_get(v_a_153_, 1);
v_lparams_155_ = lean_ctor_get(v_a_153_, 2);
v_ngen_156_ = lean_ctor_get(v_a_153_, 3);
v_safety_157_ = lean_ctor_get_uint8(v_a_153_, sizeof(void*)*4);
v_allowPrimitive_158_ = lean_ctor_get_uint8(v_a_153_, sizeof(void*)*4 + 1);
lean_inc_ref(v_ngen_156_);
lean_inc(v_lparams_155_);
lean_inc_ref(v_lctx_154_);
v___x_159_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_159_, 0, v_env_151_);
lean_ctor_set(v___x_159_, 1, v_lctx_154_);
lean_ctor_set(v___x_159_, 2, v_lparams_155_);
lean_ctor_set(v___x_159_, 3, v_ngen_156_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*4, v_safety_157_);
lean_ctor_set_uint8(v___x_159_, sizeof(void*)*4 + 1, v_allowPrimitive_158_);
v___x_160_ = lean_apply_1(v_x_152_, v___x_159_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_withEnv___boxed(lean_object* v_00_u03b1_161_, lean_object* v_env_162_, lean_object* v_x_163_, lean_object* v_a_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean4Lean_AddInductive_withEnv(v_00_u03b1_161_, v_env_162_, v_x_163_, v_a_164_);
lean_dec_ref(v_a_164_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getType(lean_object* v_fvar_166_, lean_object* v_a_167_){
_start:
{
lean_object* v_lctx_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_lctx_168_ = lean_ctor_get(v_a_167_, 1);
v___x_169_ = l_Lean_Expr_fvarId_x21(v_fvar_166_);
lean_inc_ref(v_lctx_168_);
v___x_170_ = l_Lean_LocalContext_get_x21(v_lctx_168_, v___x_169_);
v___x_171_ = l_Lean_LocalDecl_type(v___x_170_);
lean_dec_ref(v___x_170_);
v___x_172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
return v___x_172_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getType___boxed(lean_object* v_fvar_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lean4Lean_AddInductive_getType(v_fvar_173_, v_a_174_);
lean_dec_ref(v_a_174_);
lean_dec_ref(v_fvar_173_);
return v_res_175_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg(lean_object* v_nparams_188_, lean_object* v_stats_189_, lean_object* v_type_190_, lean_object* v_i_191_, lean_object* v_nindices_192_, lean_object* v_fuel_193_, lean_object* v_k_194_, lean_object* v_a_195_){
_start:
{
lean_object* v_zero_196_; uint8_t v_isZero_197_; 
v_zero_196_ = lean_unsigned_to_nat(0u);
v_isZero_197_ = lean_nat_dec_eq(v_fuel_193_, v_zero_196_);
if (v_isZero_197_ == 1)
{
lean_object* v___x_198_; 
lean_dec_ref(v_a_195_);
lean_dec_ref(v_k_194_);
lean_dec(v_fuel_193_);
lean_dec(v_nindices_192_);
lean_dec(v_i_191_);
lean_dec_ref(v_type_190_);
lean_dec_ref(v_stats_189_);
v___x_198_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__0));
return v___x_198_;
}
else
{
if (lean_obj_tag(v_type_190_) == 7)
{
lean_object* v_binderName_199_; lean_object* v_binderType_200_; lean_object* v_body_201_; uint8_t v_binderInfo_202_; uint8_t v___x_203_; lean_object* v_one_204_; lean_object* v_n_205_; 
v_binderName_199_ = lean_ctor_get(v_type_190_, 0);
lean_inc(v_binderName_199_);
v_binderType_200_ = lean_ctor_get(v_type_190_, 1);
lean_inc_ref(v_binderType_200_);
v_body_201_ = lean_ctor_get(v_type_190_, 2);
lean_inc_ref(v_body_201_);
v_binderInfo_202_ = lean_ctor_get_uint8(v_type_190_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_190_);
v___x_203_ = lean_nat_dec_lt(v_i_191_, v_nparams_188_);
v_one_204_ = lean_unsigned_to_nat(1u);
v_n_205_ = lean_nat_sub(v_fuel_193_, v_one_204_);
lean_dec(v_fuel_193_);
if (v___x_203_ == 0)
{
lean_object* v_ngen_206_; lean_object* v_env_207_; lean_object* v_lctx_208_; lean_object* v_lparams_209_; uint8_t v_safety_210_; uint8_t v_allowPrimitive_211_; lean_object* v_namePrefix_212_; lean_object* v_idx_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v_type_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_ngen_206_ = lean_ctor_get(v_a_195_, 3);
lean_inc_ref(v_ngen_206_);
v_env_207_ = lean_ctor_get(v_a_195_, 0);
lean_inc_ref_n(v_env_207_, 2);
v_lctx_208_ = lean_ctor_get(v_a_195_, 1);
lean_inc_ref(v_lctx_208_);
v_lparams_209_ = lean_ctor_get(v_a_195_, 2);
lean_inc_n(v_lparams_209_, 2);
v_safety_210_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*4);
v_allowPrimitive_211_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_195_);
v_namePrefix_212_ = lean_ctor_get(v_ngen_206_, 0);
lean_inc_n(v_namePrefix_212_, 2);
v_idx_213_ = lean_ctor_get(v_ngen_206_, 1);
lean_inc_n(v_idx_213_, 2);
lean_dec_ref(v_ngen_206_);
v___x_214_ = lean_expr_consume_type_annotations(v_binderType_200_);
v___x_215_ = l_Lean_Name_num___override(v_namePrefix_212_, v_idx_213_);
v___x_216_ = lean_nat_add(v_idx_213_, v_one_204_);
lean_dec(v_idx_213_);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_namePrefix_212_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
lean_inc(v___x_215_);
v___x_218_ = l_Lean_Expr_fvar___override(v___x_215_);
v___x_219_ = 0;
v___x_220_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_208_, v___x_215_, v_binderName_199_, v___x_214_, v_binderInfo_202_, v___x_219_);
lean_inc_ref(v___x_220_);
v___x_221_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_221_, 0, v_env_207_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
lean_ctor_set(v___x_221_, 2, v_lparams_209_);
lean_ctor_set(v___x_221_, 3, v___x_217_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*4, v_safety_210_);
lean_ctor_set_uint8(v___x_221_, sizeof(void*)*4 + 1, v_allowPrimitive_211_);
v_type_222_ = lean_expr_instantiate1(v_body_201_, v___x_218_);
lean_dec_ref(v___x_218_);
lean_dec_ref(v_body_201_);
v___x_223_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_223_, 0, v_type_222_);
v___x_224_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_207_, v_safety_210_, v___x_220_, v_lparams_209_, v___x_223_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
lean_dec_ref(v___x_221_);
lean_dec(v_n_205_);
lean_dec_ref(v_k_194_);
lean_dec(v_nindices_192_);
lean_dec(v_i_191_);
lean_dec_ref(v_stats_189_);
v_a_225_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_224_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_224_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
else
{
lean_object* v_a_233_; lean_object* v___x_234_; 
v_a_233_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_233_);
lean_dec_ref(v___x_224_);
v___x_234_ = lean_nat_add(v_nindices_192_, v_one_204_);
lean_dec(v_nindices_192_);
v_type_190_ = v_a_233_;
v_nindices_192_ = v___x_234_;
v_fuel_193_ = v_n_205_;
v_a_195_ = v___x_221_;
goto _start;
}
}
else
{
lean_object* v_lctx_236_; lean_object* v_levels_237_; lean_object* v_resultLevel_238_; lean_object* v_nindices_239_; lean_object* v_indConsts_240_; lean_object* v_params_241_; uint8_t v_isNotZero_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_lctx_236_ = lean_ctor_get(v_stats_189_, 0);
v_levels_237_ = lean_ctor_get(v_stats_189_, 1);
v_resultLevel_238_ = lean_ctor_get(v_stats_189_, 2);
v_nindices_239_ = lean_ctor_get(v_stats_189_, 3);
v_indConsts_240_ = lean_ctor_get(v_stats_189_, 4);
v_params_241_ = lean_ctor_get(v_stats_189_, 5);
v_isNotZero_242_ = lean_ctor_get_uint8(v_stats_189_, sizeof(void*)*6);
v___x_243_ = lean_array_get_size(v_indConsts_240_);
v___x_244_ = lean_nat_dec_eq(v___x_243_, v_zero_196_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; lean_object* v_param_246_; lean_object* v___x_247_; lean_object* v_a_248_; lean_object* v_env_249_; lean_object* v_lctx_250_; lean_object* v_lparams_251_; uint8_t v_safety_252_; lean_object* v___x_253_; lean_object* v___x_254_; 
lean_dec(v_binderName_199_);
v___x_245_ = l_Lean_instInhabitedExpr;
v_param_246_ = lean_array_get_borrowed(v___x_245_, v_params_241_, v_i_191_);
v___x_247_ = l_Lean4Lean_AddInductive_getType(v_param_246_, v_a_195_);
v_a_248_ = lean_ctor_get(v___x_247_, 0);
lean_inc(v_a_248_);
lean_dec_ref(v___x_247_);
v_env_249_ = lean_ctor_get(v_a_195_, 0);
v_lctx_250_ = lean_ctor_get(v_a_195_, 1);
v_lparams_251_ = lean_ctor_get(v_a_195_, 2);
v_safety_252_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*4);
v___x_253_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_isDefEq___boxed), 4, 2);
lean_closure_set(v___x_253_, 0, v_binderType_200_);
lean_closure_set(v___x_253_, 1, v_a_248_);
lean_inc(v_lparams_251_);
lean_inc_ref(v_lctx_250_);
lean_inc_ref(v_env_249_);
v___x_254_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_249_, v_safety_252_, v_lctx_250_, v_lparams_251_, v___x_253_);
if (lean_obj_tag(v___x_254_) == 0)
{
lean_object* v_a_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_262_; 
lean_dec(v_n_205_);
lean_dec_ref(v_body_201_);
lean_dec_ref(v_a_195_);
lean_dec_ref(v_k_194_);
lean_dec(v_nindices_192_);
lean_dec(v_i_191_);
lean_dec_ref(v_stats_189_);
v_a_255_ = lean_ctor_get(v___x_254_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_254_);
if (v_isSharedCheck_262_ == 0)
{
v___x_257_ = v___x_254_;
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_a_255_);
lean_dec(v___x_254_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_262_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___x_260_; 
if (v_isShared_258_ == 0)
{
v___x_260_ = v___x_257_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
else
{
lean_object* v_a_263_; uint8_t v___x_264_; 
v_a_263_ = lean_ctor_get(v___x_254_, 0);
lean_inc(v_a_263_);
lean_dec_ref(v___x_254_);
v___x_264_ = lean_unbox(v_a_263_);
lean_dec(v_a_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_n_205_);
lean_dec_ref(v_body_201_);
lean_dec_ref(v_a_195_);
lean_dec_ref(v_k_194_);
lean_dec(v_nindices_192_);
lean_dec(v_i_191_);
lean_dec_ref(v_stats_189_);
v___x_265_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__3));
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = lean_expr_instantiate1(v_body_201_, v_param_246_);
lean_dec_ref(v_body_201_);
v___x_267_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_267_, 0, v___x_266_);
lean_inc(v_lparams_251_);
lean_inc_ref(v_lctx_250_);
lean_inc_ref(v_env_249_);
v___x_268_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_249_, v_safety_252_, v_lctx_250_, v_lparams_251_, v___x_267_);
if (lean_obj_tag(v___x_268_) == 0)
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_n_205_);
lean_dec_ref(v_a_195_);
lean_dec_ref(v_k_194_);
lean_dec(v_nindices_192_);
lean_dec(v_i_191_);
lean_dec_ref(v_stats_189_);
v_a_269_ = lean_ctor_get(v___x_268_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_268_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_268_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_268_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_278_; 
v_a_277_ = lean_ctor_get(v___x_268_, 0);
lean_inc(v_a_277_);
lean_dec_ref(v___x_268_);
v___x_278_ = lean_nat_add(v_i_191_, v_one_204_);
lean_dec(v_i_191_);
v_type_190_ = v_a_277_;
v_i_191_ = v___x_278_;
v_fuel_193_ = v_n_205_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_317_; 
lean_inc_ref(v_params_241_);
lean_inc_ref(v_indConsts_240_);
lean_inc_ref(v_nindices_239_);
lean_inc(v_resultLevel_238_);
lean_inc(v_levels_237_);
lean_inc_ref(v_lctx_236_);
v_isSharedCheck_317_ = !lean_is_exclusive(v_stats_189_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; lean_object* v_unused_319_; lean_object* v_unused_320_; lean_object* v_unused_321_; lean_object* v_unused_322_; lean_object* v_unused_323_; 
v_unused_318_ = lean_ctor_get(v_stats_189_, 5);
lean_dec(v_unused_318_);
v_unused_319_ = lean_ctor_get(v_stats_189_, 4);
lean_dec(v_unused_319_);
v_unused_320_ = lean_ctor_get(v_stats_189_, 3);
lean_dec(v_unused_320_);
v_unused_321_ = lean_ctor_get(v_stats_189_, 2);
lean_dec(v_unused_321_);
v_unused_322_ = lean_ctor_get(v_stats_189_, 1);
lean_dec(v_unused_322_);
v_unused_323_ = lean_ctor_get(v_stats_189_, 0);
lean_dec(v_unused_323_);
v___x_281_ = v_stats_189_;
v_isShared_282_ = v_isSharedCheck_317_;
goto v_resetjp_280_;
}
else
{
lean_dec(v_stats_189_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_317_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v_ngen_283_; lean_object* v_env_284_; lean_object* v_lctx_285_; lean_object* v_lparams_286_; uint8_t v_safety_287_; uint8_t v_allowPrimitive_288_; lean_object* v_namePrefix_289_; lean_object* v_idx_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_type_299_; lean_object* v___x_300_; lean_object* v___x_301_; 
v_ngen_283_ = lean_ctor_get(v_a_195_, 3);
lean_inc_ref(v_ngen_283_);
v_env_284_ = lean_ctor_get(v_a_195_, 0);
lean_inc_ref_n(v_env_284_, 2);
v_lctx_285_ = lean_ctor_get(v_a_195_, 1);
lean_inc_ref(v_lctx_285_);
v_lparams_286_ = lean_ctor_get(v_a_195_, 2);
lean_inc_n(v_lparams_286_, 2);
v_safety_287_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*4);
v_allowPrimitive_288_ = lean_ctor_get_uint8(v_a_195_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_195_);
v_namePrefix_289_ = lean_ctor_get(v_ngen_283_, 0);
lean_inc_n(v_namePrefix_289_, 2);
v_idx_290_ = lean_ctor_get(v_ngen_283_, 1);
lean_inc_n(v_idx_290_, 2);
lean_dec_ref(v_ngen_283_);
v___x_291_ = lean_expr_consume_type_annotations(v_binderType_200_);
v___x_292_ = l_Lean_Name_num___override(v_namePrefix_289_, v_idx_290_);
v___x_293_ = lean_nat_add(v_idx_290_, v_one_204_);
lean_dec(v_idx_290_);
v___x_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_294_, 0, v_namePrefix_289_);
lean_ctor_set(v___x_294_, 1, v___x_293_);
lean_inc(v___x_292_);
v___x_295_ = l_Lean_Expr_fvar___override(v___x_292_);
v___x_296_ = 0;
v___x_297_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_285_, v___x_292_, v_binderName_199_, v___x_291_, v_binderInfo_202_, v___x_296_);
lean_inc_ref(v___x_297_);
v___x_298_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_298_, 0, v_env_284_);
lean_ctor_set(v___x_298_, 1, v___x_297_);
lean_ctor_set(v___x_298_, 2, v_lparams_286_);
lean_ctor_set(v___x_298_, 3, v___x_294_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*4, v_safety_287_);
lean_ctor_set_uint8(v___x_298_, sizeof(void*)*4 + 1, v_allowPrimitive_288_);
v_type_299_ = lean_expr_instantiate1(v_body_201_, v___x_295_);
lean_dec_ref(v_body_201_);
v___x_300_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_300_, 0, v_type_299_);
v___x_301_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_284_, v_safety_287_, v___x_297_, v_lparams_286_, v___x_300_);
if (lean_obj_tag(v___x_301_) == 0)
{
lean_object* v_a_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_309_; 
lean_dec_ref(v___x_298_);
lean_dec_ref(v___x_295_);
lean_del_object(v___x_281_);
lean_dec_ref(v_params_241_);
lean_dec_ref(v_indConsts_240_);
lean_dec_ref(v_nindices_239_);
lean_dec(v_resultLevel_238_);
lean_dec(v_levels_237_);
lean_dec_ref(v_lctx_236_);
lean_dec(v_n_205_);
lean_dec_ref(v_k_194_);
lean_dec(v_nindices_192_);
lean_dec(v_i_191_);
v_a_302_ = lean_ctor_get(v___x_301_, 0);
v_isSharedCheck_309_ = !lean_is_exclusive(v___x_301_);
if (v_isSharedCheck_309_ == 0)
{
v___x_304_ = v___x_301_;
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_a_302_);
lean_dec(v___x_301_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_309_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_307_; 
if (v_isShared_305_ == 0)
{
v___x_307_ = v___x_304_;
goto v_reusejp_306_;
}
else
{
lean_object* v_reuseFailAlloc_308_; 
v_reuseFailAlloc_308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_308_, 0, v_a_302_);
v___x_307_ = v_reuseFailAlloc_308_;
goto v_reusejp_306_;
}
v_reusejp_306_:
{
return v___x_307_;
}
}
}
else
{
lean_object* v_a_310_; lean_object* v___x_311_; lean_object* v_stats_313_; 
v_a_310_ = lean_ctor_get(v___x_301_, 0);
lean_inc(v_a_310_);
lean_dec_ref(v___x_301_);
v___x_311_ = lean_array_push(v_params_241_, v___x_295_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 5, v___x_311_);
v_stats_313_ = v___x_281_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_lctx_236_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_levels_237_);
lean_ctor_set(v_reuseFailAlloc_316_, 2, v_resultLevel_238_);
lean_ctor_set(v_reuseFailAlloc_316_, 3, v_nindices_239_);
lean_ctor_set(v_reuseFailAlloc_316_, 4, v_indConsts_240_);
lean_ctor_set(v_reuseFailAlloc_316_, 5, v___x_311_);
lean_ctor_set_uint8(v_reuseFailAlloc_316_, sizeof(void*)*6, v_isNotZero_242_);
v_stats_313_ = v_reuseFailAlloc_316_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
lean_object* v___x_314_; 
v___x_314_ = lean_nat_add(v_i_191_, v_one_204_);
lean_dec(v_i_191_);
v_stats_189_ = v_stats_313_;
v_type_190_ = v_a_310_;
v_i_191_ = v___x_314_;
v_fuel_193_ = v_n_205_;
v_a_195_ = v___x_298_;
goto _start;
}
}
}
}
}
}
else
{
uint8_t v___x_324_; 
lean_dec(v_fuel_193_);
v___x_324_ = lean_nat_dec_eq(v_i_191_, v_nparams_188_);
lean_dec(v_i_191_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; 
lean_dec_ref(v_a_195_);
lean_dec_ref(v_k_194_);
lean_dec(v_nindices_192_);
lean_dec_ref(v_type_190_);
lean_dec_ref(v_stats_189_);
v___x_325_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__6));
return v___x_325_;
}
else
{
lean_object* v___x_326_; 
v___x_326_ = lean_apply_4(v_k_194_, v_type_190_, v_stats_189_, v_nindices_192_, v_a_195_);
return v___x_326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___boxed(lean_object* v_nparams_327_, lean_object* v_stats_328_, lean_object* v_type_329_, lean_object* v_i_330_, lean_object* v_nindices_331_, lean_object* v_fuel_332_, lean_object* v_k_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg(v_nparams_327_, v_stats_328_, v_type_329_, v_i_330_, v_nindices_331_, v_fuel_332_, v_k_333_, v_a_334_);
lean_dec(v_nparams_327_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop(lean_object* v_00_u03b1_336_, lean_object* v_nparams_337_, lean_object* v_stats_338_, lean_object* v_type_339_, lean_object* v_i_340_, lean_object* v_nindices_341_, lean_object* v_fuel_342_, lean_object* v_k_343_, lean_object* v_a_344_){
_start:
{
lean_object* v___x_345_; 
lean_inc_ref(v_a_344_);
v___x_345_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg(v_nparams_337_, v_stats_338_, v_type_339_, v_i_340_, v_nindices_341_, v_fuel_342_, v_k_343_, v_a_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___boxed(lean_object* v_00_u03b1_346_, lean_object* v_nparams_347_, lean_object* v_stats_348_, lean_object* v_type_349_, lean_object* v_i_350_, lean_object* v_nindices_351_, lean_object* v_fuel_352_, lean_object* v_k_353_, lean_object* v_a_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop(v_00_u03b1_346_, v_nparams_347_, v_stats_348_, v_type_349_, v_i_350_, v_nindices_351_, v_fuel_352_, v_k_353_, v_a_354_);
lean_dec_ref(v_a_354_);
lean_dec(v_nparams_347_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_AddInductive_checkInductiveTypes_loopInd_spec__0(lean_object* v_msg_356_){
_start:
{
lean_object* v___x_357_; lean_object* v___x_358_; 
v___x_357_ = l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default;
v___x_358_ = lean_panic_fn_borrowed(v___x_357_, v_msg_356_);
return v___x_358_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__3(void){
_start:
{
lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_367_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__2));
v___x_368_ = lean_unsigned_to_nat(8u);
v___x_369_ = lean_unsigned_to_nat(111u);
v___x_370_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__1));
v___x_371_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_372_ = l_mkPanicMessageWithDecl(v___x_371_, v___x_370_, v___x_369_, v___x_368_, v___x_367_);
return v___x_372_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__5(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_374_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__4));
v___x_375_ = lean_unsigned_to_nat(8u);
v___x_376_ = lean_unsigned_to_nat(112u);
v___x_377_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__1));
v___x_378_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_379_ = l_mkPanicMessageWithDecl(v___x_378_, v___x_377_, v___x_376_, v___x_375_, v___x_374_);
return v___x_379_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__7(void){
_start:
{
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
v___x_381_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__6));
v___x_382_ = lean_unsigned_to_nat(8u);
v___x_383_ = lean_unsigned_to_nat(113u);
v___x_384_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__1));
v___x_385_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_386_ = l_mkPanicMessageWithDecl(v___x_385_, v___x_384_, v___x_383_, v___x_382_, v___x_381_);
return v___x_386_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__9(void){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v___x_388_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__8));
v___x_389_ = lean_unsigned_to_nat(8u);
v___x_390_ = lean_unsigned_to_nat(114u);
v___x_391_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__1));
v___x_392_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_393_ = l_mkPanicMessageWithDecl(v___x_392_, v___x_391_, v___x_390_, v___x_389_, v___x_388_);
return v___x_393_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___boxed(lean_object* v_name_394_, lean_object* v_dIdx_395_, lean_object* v_nparams_396_, lean_object* v_indTypes_397_, lean_object* v_k_398_, lean_object* v_type_399_, lean_object* v_stats_400_, lean_object* v_nindices_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0(v_name_394_, v_dIdx_395_, v_nparams_396_, v_indTypes_397_, v_k_398_, v_type_399_, v_stats_400_, v_nindices_401_, v___y_402_);
lean_dec_ref(v___y_402_);
lean_dec(v_dIdx_395_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg(lean_object* v_nparams_404_, lean_object* v_indTypes_405_, lean_object* v_k_406_, lean_object* v_dIdx_407_, lean_object* v_stats_408_, lean_object* v_a_409_){
_start:
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = lean_array_get_size(v_indTypes_405_);
v___x_411_ = lean_nat_dec_lt(v_dIdx_407_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v_levels_412_; lean_object* v_nindices_413_; lean_object* v_indConsts_414_; lean_object* v_params_415_; lean_object* v_lparams_416_; lean_object* v___x_417_; lean_object* v___x_418_; uint8_t v___x_419_; 
lean_dec(v_dIdx_407_);
lean_dec_ref(v_indTypes_405_);
v_levels_412_ = lean_ctor_get(v_stats_408_, 1);
v_nindices_413_ = lean_ctor_get(v_stats_408_, 3);
v_indConsts_414_ = lean_ctor_get(v_stats_408_, 4);
v_params_415_ = lean_ctor_get(v_stats_408_, 5);
v_lparams_416_ = lean_ctor_get(v_a_409_, 2);
v___x_417_ = l_List_lengthTR___redArg(v_levels_412_);
v___x_418_ = l_List_lengthTR___redArg(v_lparams_416_);
v___x_419_ = lean_nat_dec_eq(v___x_417_, v___x_418_);
lean_dec(v___x_418_);
lean_dec(v___x_417_);
if (v___x_419_ == 0)
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; 
lean_dec_ref(v_stats_408_);
lean_dec(v_nparams_404_);
v___x_420_ = lean_obj_once(&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__3, &l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__3_once, _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__3);
v___x_421_ = l_panic___at___00Lean4Lean_AddInductive_checkInductiveTypes_loopInd_spec__0(v___x_420_);
lean_inc_ref(v_a_409_);
v___x_422_ = lean_apply_2(v_k_406_, v___x_421_, v_a_409_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; uint8_t v___x_424_; 
v___x_423_ = lean_array_get_size(v_nindices_413_);
v___x_424_ = lean_nat_dec_eq(v___x_423_, v___x_410_);
if (v___x_424_ == 0)
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec_ref(v_stats_408_);
lean_dec(v_nparams_404_);
v___x_425_ = lean_obj_once(&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__5, &l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__5_once, _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__5);
v___x_426_ = l_panic___at___00Lean4Lean_AddInductive_checkInductiveTypes_loopInd_spec__0(v___x_425_);
lean_inc_ref(v_a_409_);
v___x_427_ = lean_apply_2(v_k_406_, v___x_426_, v_a_409_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; uint8_t v___x_429_; 
v___x_428_ = lean_array_get_size(v_indConsts_414_);
v___x_429_ = lean_nat_dec_eq(v___x_428_, v___x_410_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec_ref(v_stats_408_);
lean_dec(v_nparams_404_);
v___x_430_ = lean_obj_once(&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__7, &l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__7_once, _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__7);
v___x_431_ = l_panic___at___00Lean4Lean_AddInductive_checkInductiveTypes_loopInd_spec__0(v___x_430_);
lean_inc_ref(v_a_409_);
v___x_432_ = lean_apply_2(v_k_406_, v___x_431_, v_a_409_);
return v___x_432_;
}
else
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_array_get_size(v_params_415_);
v___x_434_ = lean_nat_dec_eq(v___x_433_, v_nparams_404_);
lean_dec(v_nparams_404_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
lean_dec_ref(v_stats_408_);
v___x_435_ = lean_obj_once(&l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__9, &l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__9_once, _init_l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__9);
v___x_436_ = l_panic___at___00Lean4Lean_AddInductive_checkInductiveTypes_loopInd_spec__0(v___x_435_);
lean_inc_ref(v_a_409_);
v___x_437_ = lean_apply_2(v_k_406_, v___x_436_, v_a_409_);
return v___x_437_;
}
else
{
lean_object* v___x_438_; 
lean_inc_ref(v_a_409_);
v___x_438_ = lean_apply_2(v_k_406_, v_stats_408_, v_a_409_);
return v___x_438_;
}
}
}
}
}
else
{
lean_object* v_env_439_; lean_object* v_lctx_440_; lean_object* v_lparams_441_; uint8_t v_safety_442_; lean_object* v_indType_443_; lean_object* v_name_444_; lean_object* v_type_445_; lean_object* v___x_446_; 
v_env_439_ = lean_ctor_get(v_a_409_, 0);
v_lctx_440_ = lean_ctor_get(v_a_409_, 1);
v_lparams_441_ = lean_ctor_get(v_a_409_, 2);
v_safety_442_ = lean_ctor_get_uint8(v_a_409_, sizeof(void*)*4);
v_indType_443_ = lean_array_fget_borrowed(v_indTypes_405_, v_dIdx_407_);
v_name_444_ = lean_ctor_get(v_indType_443_, 0);
lean_inc_n(v_name_444_, 2);
v_type_445_ = lean_ctor_get(v_indType_443_, 1);
lean_inc_ref(v_type_445_);
lean_inc_ref(v_env_439_);
v___x_446_ = l_Lean_Kernel_Environment_checkNoMVarNoFVar(v_env_439_, v_name_444_, v_type_445_);
if (lean_obj_tag(v___x_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_449_; uint8_t v_isShared_450_; uint8_t v_isSharedCheck_454_; 
lean_dec(v_name_444_);
lean_dec_ref(v_stats_408_);
lean_dec(v_dIdx_407_);
lean_dec_ref(v_k_406_);
lean_dec_ref(v_indTypes_405_);
lean_dec(v_nparams_404_);
v_a_447_ = lean_ctor_get(v___x_446_, 0);
v_isSharedCheck_454_ = !lean_is_exclusive(v___x_446_);
if (v_isSharedCheck_454_ == 0)
{
v___x_449_ = v___x_446_;
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
else
{
lean_inc(v_a_447_);
lean_dec(v___x_446_);
v___x_449_ = lean_box(0);
v_isShared_450_ = v_isSharedCheck_454_;
goto v_resetjp_448_;
}
v_resetjp_448_:
{
lean_object* v___x_452_; 
if (v_isShared_450_ == 0)
{
v___x_452_ = v___x_449_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
}
else
{
lean_object* v___x_455_; lean_object* v___x_456_; 
lean_dec_ref(v___x_446_);
lean_inc_ref(v_type_445_);
v___x_455_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_checkType___boxed), 3, 1);
lean_closure_set(v___x_455_, 0, v_type_445_);
lean_inc(v_lparams_441_);
lean_inc_ref(v_lctx_440_);
lean_inc_ref(v_env_439_);
v___x_456_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_439_, v_safety_442_, v_lctx_440_, v_lparams_441_, v___x_455_);
if (lean_obj_tag(v___x_456_) == 0)
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
lean_dec(v_name_444_);
lean_dec_ref(v_stats_408_);
lean_dec(v_dIdx_407_);
lean_dec_ref(v_k_406_);
lean_dec_ref(v_indTypes_405_);
lean_dec(v_nparams_404_);
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
else
{
lean_object* v___x_465_; lean_object* v___x_466_; 
lean_dec_ref(v___x_456_);
lean_inc_ref(v_type_445_);
v___x_465_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_465_, 0, v_type_445_);
lean_inc(v_lparams_441_);
lean_inc_ref(v_lctx_440_);
lean_inc_ref(v_env_439_);
v___x_466_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_439_, v_safety_442_, v_lctx_440_, v_lparams_441_, v___x_465_);
if (lean_obj_tag(v___x_466_) == 0)
{
lean_object* v_a_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_474_; 
lean_dec(v_name_444_);
lean_dec_ref(v_stats_408_);
lean_dec(v_dIdx_407_);
lean_dec_ref(v_k_406_);
lean_dec_ref(v_indTypes_405_);
lean_dec(v_nparams_404_);
v_a_467_ = lean_ctor_get(v___x_466_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v___x_466_);
if (v_isSharedCheck_474_ == 0)
{
v___x_469_ = v___x_466_;
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_a_467_);
lean_dec(v___x_466_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_474_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_472_; 
if (v_isShared_470_ == 0)
{
v___x_472_ = v___x_469_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v_a_467_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
else
{
lean_object* v_a_475_; lean_object* v___f_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; 
v_a_475_ = lean_ctor_get(v___x_466_, 0);
lean_inc(v_a_475_);
lean_dec_ref(v___x_466_);
lean_inc(v_nparams_404_);
v___f_476_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___boxed), 9, 5);
lean_closure_set(v___f_476_, 0, v_name_444_);
lean_closure_set(v___f_476_, 1, v_dIdx_407_);
lean_closure_set(v___f_476_, 2, v_nparams_404_);
lean_closure_set(v___f_476_, 3, v_indTypes_405_);
lean_closure_set(v___f_476_, 4, v_k_406_);
v___x_477_ = lean_unsigned_to_nat(0u);
v___x_478_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v_a_409_);
v___x_479_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg(v_nparams_404_, v_stats_408_, v_a_475_, v___x_477_, v___x_477_, v___x_478_, v___f_476_, v_a_409_);
lean_dec(v_nparams_404_);
return v___x_479_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0(lean_object* v_name_480_, lean_object* v_dIdx_481_, lean_object* v_nparams_482_, lean_object* v_indTypes_483_, lean_object* v_k_484_, lean_object* v_type_485_, lean_object* v_stats_486_, lean_object* v_nindices_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_lctx_490_; lean_object* v_levels_491_; lean_object* v_resultLevel_492_; lean_object* v_nindices_493_; lean_object* v_indConsts_494_; lean_object* v_params_495_; uint8_t v_isNotZero_496_; lean_object* v___y_497_; lean_object* v___x_507_; lean_object* v_env_508_; lean_object* v_lctx_509_; lean_object* v_lparams_510_; uint8_t v_safety_511_; lean_object* v___x_512_; 
lean_inc_ref(v_type_485_);
v___x_507_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_ensureSort___boxed), 4, 2);
lean_closure_set(v___x_507_, 0, v_type_485_);
lean_closure_set(v___x_507_, 1, v_type_485_);
v_env_508_ = lean_ctor_get(v___y_488_, 0);
v_lctx_509_ = lean_ctor_get(v___y_488_, 1);
v_lparams_510_ = lean_ctor_get(v___y_488_, 2);
v_safety_511_ = lean_ctor_get_uint8(v___y_488_, sizeof(void*)*4);
lean_inc(v_lparams_510_);
lean_inc_ref(v_lctx_509_);
lean_inc_ref(v_env_508_);
v___x_512_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_508_, v_safety_511_, v_lctx_509_, v_lparams_510_, v___x_507_);
if (lean_obj_tag(v___x_512_) == 0)
{
lean_object* v_a_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_nindices_487_);
lean_dec_ref(v_stats_486_);
lean_dec_ref(v_k_484_);
lean_dec_ref(v_indTypes_483_);
lean_dec(v_nparams_482_);
lean_dec(v_name_480_);
v_a_513_ = lean_ctor_get(v___x_512_, 0);
v_isSharedCheck_520_ = !lean_is_exclusive(v___x_512_);
if (v_isSharedCheck_520_ == 0)
{
v___x_515_ = v___x_512_;
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_a_513_);
lean_dec(v___x_512_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_520_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v___x_518_; 
if (v_isShared_516_ == 0)
{
v___x_518_ = v___x_515_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_513_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
else
{
lean_object* v_a_521_; lean_object* v_lctx_522_; lean_object* v_levels_523_; lean_object* v_resultLevel_524_; lean_object* v_nindices_525_; lean_object* v_indConsts_526_; lean_object* v_params_527_; uint8_t v_isNotZero_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; uint8_t v___x_532_; 
v_a_521_ = lean_ctor_get(v___x_512_, 0);
lean_inc(v_a_521_);
lean_dec_ref(v___x_512_);
v_lctx_522_ = lean_ctor_get(v_stats_486_, 0);
lean_inc_ref(v_lctx_522_);
v_levels_523_ = lean_ctor_get(v_stats_486_, 1);
lean_inc(v_levels_523_);
v_resultLevel_524_ = lean_ctor_get(v_stats_486_, 2);
lean_inc(v_resultLevel_524_);
v_nindices_525_ = lean_ctor_get(v_stats_486_, 3);
lean_inc_ref(v_nindices_525_);
v_indConsts_526_ = lean_ctor_get(v_stats_486_, 4);
lean_inc_ref(v_indConsts_526_);
v_params_527_ = lean_ctor_get(v_stats_486_, 5);
lean_inc_ref(v_params_527_);
v_isNotZero_528_ = lean_ctor_get_uint8(v_stats_486_, sizeof(void*)*6);
lean_dec_ref(v_stats_486_);
v___x_529_ = l_Lean_Expr_sortLevel_x21(v_a_521_);
lean_dec(v_a_521_);
v___x_530_ = lean_array_get_size(v_indConsts_526_);
v___x_531_ = lean_unsigned_to_nat(0u);
v___x_532_ = lean_nat_dec_eq(v___x_530_, v___x_531_);
if (v___x_532_ == 0)
{
uint8_t v___x_533_; 
lean_inc(v_resultLevel_524_);
v___x_533_ = l_Lean_Level_isEquiv_x27(v___x_529_, v_resultLevel_524_);
if (v___x_533_ == 0)
{
lean_dec_ref(v_params_527_);
lean_dec_ref(v_indConsts_526_);
lean_dec_ref(v_nindices_525_);
lean_dec(v_resultLevel_524_);
lean_dec(v_levels_523_);
lean_dec_ref(v_lctx_522_);
lean_dec(v_nindices_487_);
lean_dec_ref(v_k_484_);
lean_dec_ref(v_indTypes_483_);
lean_dec(v_nparams_482_);
lean_dec(v_name_480_);
goto v___jp_505_;
}
else
{
if (v___x_532_ == 0)
{
v_lctx_490_ = v_lctx_522_;
v_levels_491_ = v_levels_523_;
v_resultLevel_492_ = v_resultLevel_524_;
v_nindices_493_ = v_nindices_525_;
v_indConsts_494_ = v_indConsts_526_;
v_params_495_ = v_params_527_;
v_isNotZero_496_ = v_isNotZero_528_;
v___y_497_ = v___y_488_;
goto v___jp_489_;
}
else
{
lean_dec_ref(v_params_527_);
lean_dec_ref(v_indConsts_526_);
lean_dec_ref(v_nindices_525_);
lean_dec(v_resultLevel_524_);
lean_dec(v_levels_523_);
lean_dec_ref(v_lctx_522_);
lean_dec(v_nindices_487_);
lean_dec_ref(v_k_484_);
lean_dec_ref(v_indTypes_483_);
lean_dec(v_nparams_482_);
lean_dec(v_name_480_);
goto v___jp_505_;
}
}
}
else
{
uint8_t v___x_534_; 
lean_dec(v_resultLevel_524_);
lean_dec_ref(v_lctx_522_);
v___x_534_ = l_Lean_Level_isNeverZero(v___x_529_);
lean_inc_ref(v_lctx_509_);
v_lctx_490_ = v_lctx_509_;
v_levels_491_ = v_levels_523_;
v_resultLevel_492_ = v___x_529_;
v_nindices_493_ = v_nindices_525_;
v_indConsts_494_ = v_indConsts_526_;
v_params_495_ = v_params_527_;
v_isNotZero_496_ = v___x_534_;
v___y_497_ = v___y_488_;
goto v___jp_489_;
}
}
v___jp_489_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_498_ = lean_array_push(v_nindices_493_, v_nindices_487_);
lean_inc(v_levels_491_);
v___x_499_ = l_Lean_Expr_const___override(v_name_480_, v_levels_491_);
v___x_500_ = lean_array_push(v_indConsts_494_, v___x_499_);
v___x_501_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_501_, 0, v_lctx_490_);
lean_ctor_set(v___x_501_, 1, v_levels_491_);
lean_ctor_set(v___x_501_, 2, v_resultLevel_492_);
lean_ctor_set(v___x_501_, 3, v___x_498_);
lean_ctor_set(v___x_501_, 4, v___x_500_);
lean_ctor_set(v___x_501_, 5, v_params_495_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*6, v_isNotZero_496_);
v___x_502_ = lean_unsigned_to_nat(1u);
v___x_503_ = lean_nat_add(v_dIdx_481_, v___x_502_);
v___x_504_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg(v_nparams_482_, v_indTypes_483_, v_k_484_, v___x_503_, v___x_501_, v___y_497_);
return v___x_504_;
}
v___jp_505_:
{
lean_object* v___x_506_; 
v___x_506_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___lam__0___closed__2));
return v___x_506_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___boxed(lean_object* v_nparams_535_, lean_object* v_indTypes_536_, lean_object* v_k_537_, lean_object* v_dIdx_538_, lean_object* v_stats_539_, lean_object* v_a_540_){
_start:
{
lean_object* v_res_541_; 
v_res_541_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg(v_nparams_535_, v_indTypes_536_, v_k_537_, v_dIdx_538_, v_stats_539_, v_a_540_);
lean_dec_ref(v_a_540_);
return v_res_541_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd(lean_object* v_00_u03b1_542_, lean_object* v_nparams_543_, lean_object* v_indTypes_544_, lean_object* v_k_545_, lean_object* v_dIdx_546_, lean_object* v_stats_547_, lean_object* v_a_548_){
_start:
{
lean_object* v___x_549_; 
v___x_549_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg(v_nparams_543_, v_indTypes_544_, v_k_545_, v_dIdx_546_, v_stats_547_, v_a_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___boxed(lean_object* v_00_u03b1_550_, lean_object* v_nparams_551_, lean_object* v_indTypes_552_, lean_object* v_k_553_, lean_object* v_dIdx_554_, lean_object* v_stats_555_, lean_object* v_a_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd(v_00_u03b1_550_, v_nparams_551_, v_indTypes_552_, v_k_553_, v_dIdx_554_, v_stats_555_, v_a_556_);
lean_dec_ref(v_a_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean4Lean_AddInductive_checkInductiveTypes_spec__0(lean_object* v_a_558_, lean_object* v_a_559_){
_start:
{
if (lean_obj_tag(v_a_558_) == 0)
{
lean_object* v___x_560_; 
v___x_560_ = l_List_reverse___redArg(v_a_559_);
return v___x_560_;
}
else
{
lean_object* v_head_561_; lean_object* v_tail_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_571_; 
v_head_561_ = lean_ctor_get(v_a_558_, 0);
v_tail_562_ = lean_ctor_get(v_a_558_, 1);
v_isSharedCheck_571_ = !lean_is_exclusive(v_a_558_);
if (v_isSharedCheck_571_ == 0)
{
v___x_564_ = v_a_558_;
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_tail_562_);
lean_inc(v_head_561_);
lean_dec(v_a_558_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_571_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v___x_568_; 
v___x_566_ = l_Lean_Level_param___override(v_head_561_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 1, v_a_559_);
lean_ctor_set(v___x_564_, 0, v___x_566_);
v___x_568_ = v___x_564_;
goto v_reusejp_567_;
}
else
{
lean_object* v_reuseFailAlloc_570_; 
v_reuseFailAlloc_570_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_570_, 0, v___x_566_);
lean_ctor_set(v_reuseFailAlloc_570_, 1, v_a_559_);
v___x_568_ = v_reuseFailAlloc_570_;
goto v_reusejp_567_;
}
v_reusejp_567_:
{
v_a_558_ = v_tail_562_;
v_a_559_ = v___x_568_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes___redArg(lean_object* v_nparams_572_, lean_object* v_indTypes_573_, lean_object* v_k_574_, lean_object* v_a_575_){
_start:
{
lean_object* v___x_576_; lean_object* v_lctx_577_; lean_object* v_nindices_578_; lean_object* v_indConsts_579_; lean_object* v_params_580_; uint8_t v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v_lparams_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_576_ = l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default;
v_lctx_577_ = lean_ctor_get(v___x_576_, 0);
v_nindices_578_ = lean_ctor_get(v___x_576_, 3);
v_indConsts_579_ = lean_ctor_get(v___x_576_, 4);
v_params_580_ = lean_ctor_get(v___x_576_, 5);
v___x_581_ = 0;
v___x_582_ = lean_box(0);
v___x_583_ = lean_box(0);
v_lparams_584_ = lean_ctor_get(v_a_575_, 2);
v___x_585_ = lean_unsigned_to_nat(0u);
lean_inc(v_lparams_584_);
v___x_586_ = l_List_mapTR_loop___at___00Lean4Lean_AddInductive_checkInductiveTypes_spec__0(v_lparams_584_, v___x_583_);
lean_inc_ref(v_params_580_);
lean_inc_ref(v_indConsts_579_);
lean_inc_ref(v_nindices_578_);
lean_inc_ref(v_lctx_577_);
v___x_587_ = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(v___x_587_, 0, v_lctx_577_);
lean_ctor_set(v___x_587_, 1, v___x_586_);
lean_ctor_set(v___x_587_, 2, v___x_582_);
lean_ctor_set(v___x_587_, 3, v_nindices_578_);
lean_ctor_set(v___x_587_, 4, v_indConsts_579_);
lean_ctor_set(v___x_587_, 5, v_params_580_);
lean_ctor_set_uint8(v___x_587_, sizeof(void*)*6, v___x_581_);
v___x_588_ = l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg(v_nparams_572_, v_indTypes_573_, v_k_574_, v___x_585_, v___x_587_, v_a_575_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes___redArg___boxed(lean_object* v_nparams_589_, lean_object* v_indTypes_590_, lean_object* v_k_591_, lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean4Lean_AddInductive_checkInductiveTypes___redArg(v_nparams_589_, v_indTypes_590_, v_k_591_, v_a_592_);
lean_dec_ref(v_a_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes(lean_object* v_00_u03b1_594_, lean_object* v_nparams_595_, lean_object* v_indTypes_596_, lean_object* v_k_597_, lean_object* v_a_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean4Lean_AddInductive_checkInductiveTypes___redArg(v_nparams_595_, v_indTypes_596_, v_k_597_, v_a_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkInductiveTypes___boxed(lean_object* v_00_u03b1_600_, lean_object* v_nparams_601_, lean_object* v_indTypes_602_, lean_object* v_k_603_, lean_object* v_a_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean4Lean_AddInductive_checkInductiveTypes(v_00_u03b1_600_, v_nparams_601_, v_indTypes_602_, v_k_603_, v_a_604_);
lean_dec_ref(v_a_604_);
return v_res_605_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_hasIndOcc_spec__0(lean_object* v_declName_606_, lean_object* v_as_607_, size_t v_i_608_, size_t v_stop_609_){
_start:
{
uint8_t v___x_610_; 
v___x_610_ = lean_usize_dec_eq(v_i_608_, v_stop_609_);
if (v___x_610_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_array_uget_borrowed(v_as_607_, v_i_608_);
v___x_612_ = l_Lean_Expr_constName_x21(v___x_611_);
v___x_613_ = lean_name_eq(v___x_612_, v_declName_606_);
lean_dec(v___x_612_);
if (v___x_613_ == 0)
{
size_t v___x_614_; size_t v___x_615_; 
v___x_614_ = ((size_t)1ULL);
v___x_615_ = lean_usize_add(v_i_608_, v___x_614_);
v_i_608_ = v___x_615_;
goto _start;
}
else
{
return v___x_613_;
}
}
else
{
uint8_t v___x_617_; 
v___x_617_ = 0;
return v___x_617_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_hasIndOcc_spec__0___boxed(lean_object* v_declName_618_, lean_object* v_as_619_, lean_object* v_i_620_, lean_object* v_stop_621_){
_start:
{
size_t v_i_boxed_622_; size_t v_stop_boxed_623_; uint8_t v_res_624_; lean_object* v_r_625_; 
v_i_boxed_622_ = lean_unbox_usize(v_i_620_);
lean_dec(v_i_620_);
v_stop_boxed_623_ = lean_unbox_usize(v_stop_621_);
lean_dec(v_stop_621_);
v_res_624_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_hasIndOcc_spec__0(v_declName_618_, v_as_619_, v_i_boxed_622_, v_stop_boxed_623_);
lean_dec_ref(v_as_619_);
lean_dec(v_declName_618_);
v_r_625_ = lean_box(v_res_624_);
return v_r_625_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_hasIndOcc___lam__0(lean_object* v_indConsts_626_, lean_object* v_x_627_){
_start:
{
if (lean_obj_tag(v_x_627_) == 4)
{
lean_object* v_declName_628_; lean_object* v___x_629_; lean_object* v___x_630_; uint8_t v___x_631_; 
v_declName_628_ = lean_ctor_get(v_x_627_, 0);
v___x_629_ = lean_unsigned_to_nat(0u);
v___x_630_ = lean_array_get_size(v_indConsts_626_);
v___x_631_ = lean_nat_dec_lt(v___x_629_, v___x_630_);
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
if (v___x_631_ == 0)
{
return v___x_631_;
}
else
{
size_t v___x_632_; size_t v___x_633_; uint8_t v___x_634_; 
v___x_632_ = ((size_t)0ULL);
v___x_633_ = lean_usize_of_nat(v___x_630_);
v___x_634_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_hasIndOcc_spec__0(v_declName_628_, v_indConsts_626_, v___x_632_, v___x_633_);
return v___x_634_;
}
}
}
else
{
uint8_t v___x_635_; 
v___x_635_ = 0;
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_hasIndOcc___lam__0___boxed(lean_object* v_indConsts_636_, lean_object* v_x_637_){
_start:
{
uint8_t v_res_638_; lean_object* v_r_639_; 
v_res_638_ = l_Lean4Lean_AddInductive_hasIndOcc___lam__0(v_indConsts_636_, v_x_637_);
lean_dec_ref(v_x_637_);
lean_dec_ref(v_indConsts_636_);
v_r_639_ = lean_box(v_res_638_);
return v_r_639_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_hasIndOcc(lean_object* v_indConsts_640_, lean_object* v_t_641_){
_start:
{
lean_object* v___f_642_; lean_object* v___x_643_; 
v___f_642_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_hasIndOcc___lam__0___boxed), 2, 1);
lean_closure_set(v___f_642_, 0, v_indConsts_640_);
v___x_643_ = lean_find_expr(v___f_642_, v_t_641_);
lean_dec_ref(v___f_642_);
if (lean_obj_tag(v___x_643_) == 0)
{
uint8_t v___x_644_; 
v___x_644_ = 0;
return v___x_644_;
}
else
{
uint8_t v___x_645_; 
lean_dec_ref(v___x_643_);
v___x_645_ = 1;
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_hasIndOcc___boxed(lean_object* v_indConsts_646_, lean_object* v_t_647_){
_start:
{
uint8_t v_res_648_; lean_object* v_r_649_; 
v_res_648_ = l_Lean4Lean_AddInductive_hasIndOcc(v_indConsts_646_, v_t_647_);
lean_dec_ref(v_t_647_);
v_r_649_ = lean_box(v_res_648_);
return v_r_649_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isRec_loop(lean_object* v_indConsts_650_, lean_object* v_x_651_){
_start:
{
if (lean_obj_tag(v_x_651_) == 7)
{
lean_object* v_binderType_652_; lean_object* v_body_653_; uint8_t v___x_654_; 
v_binderType_652_ = lean_ctor_get(v_x_651_, 1);
v_body_653_ = lean_ctor_get(v_x_651_, 2);
lean_inc_ref(v_indConsts_650_);
v___x_654_ = l_Lean4Lean_AddInductive_hasIndOcc(v_indConsts_650_, v_binderType_652_);
if (v___x_654_ == 0)
{
v_x_651_ = v_body_653_;
goto _start;
}
else
{
lean_dec_ref(v_indConsts_650_);
return v___x_654_;
}
}
else
{
uint8_t v___x_656_; 
lean_dec_ref(v_indConsts_650_);
v___x_656_ = 0;
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRec_loop___boxed(lean_object* v_indConsts_657_, lean_object* v_x_658_){
_start:
{
uint8_t v_res_659_; lean_object* v_r_660_; 
v_res_659_ = l_Lean4Lean_AddInductive_isRec_loop(v_indConsts_657_, v_x_658_);
lean_dec_ref(v_x_658_);
v_r_660_ = lean_box(v_res_659_);
return v_r_660_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean4Lean_AddInductive_isRec_spec__0(lean_object* v_indConsts_661_, lean_object* v_x_662_){
_start:
{
if (lean_obj_tag(v_x_662_) == 0)
{
uint8_t v___x_663_; 
lean_dec_ref(v_indConsts_661_);
v___x_663_ = 0;
return v___x_663_;
}
else
{
lean_object* v_head_664_; lean_object* v_tail_665_; lean_object* v_type_666_; uint8_t v___x_667_; 
v_head_664_ = lean_ctor_get(v_x_662_, 0);
v_tail_665_ = lean_ctor_get(v_x_662_, 1);
v_type_666_ = lean_ctor_get(v_head_664_, 1);
lean_inc_ref(v_indConsts_661_);
v___x_667_ = l_Lean4Lean_AddInductive_isRec_loop(v_indConsts_661_, v_type_666_);
if (v___x_667_ == 0)
{
v_x_662_ = v_tail_665_;
goto _start;
}
else
{
lean_dec_ref(v_indConsts_661_);
return v___x_667_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean4Lean_AddInductive_isRec_spec__0___boxed(lean_object* v_indConsts_669_, lean_object* v_x_670_){
_start:
{
uint8_t v_res_671_; lean_object* v_r_672_; 
v_res_671_ = l_List_any___at___00Lean4Lean_AddInductive_isRec_spec__0(v_indConsts_669_, v_x_670_);
lean_dec(v_x_670_);
v_r_672_ = lean_box(v_res_671_);
return v_r_672_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isRec_spec__1(lean_object* v_indConsts_673_, lean_object* v_as_674_, size_t v_i_675_, size_t v_stop_676_){
_start:
{
uint8_t v___x_677_; 
v___x_677_ = lean_usize_dec_eq(v_i_675_, v_stop_676_);
if (v___x_677_ == 0)
{
lean_object* v___x_678_; lean_object* v_ctors_679_; uint8_t v___x_680_; 
v___x_678_ = lean_array_uget_borrowed(v_as_674_, v_i_675_);
v_ctors_679_ = lean_ctor_get(v___x_678_, 2);
lean_inc_ref(v_indConsts_673_);
v___x_680_ = l_List_any___at___00Lean4Lean_AddInductive_isRec_spec__0(v_indConsts_673_, v_ctors_679_);
if (v___x_680_ == 0)
{
size_t v___x_681_; size_t v___x_682_; 
v___x_681_ = ((size_t)1ULL);
v___x_682_ = lean_usize_add(v_i_675_, v___x_681_);
v_i_675_ = v___x_682_;
goto _start;
}
else
{
lean_dec_ref(v_indConsts_673_);
return v___x_680_;
}
}
else
{
uint8_t v___x_684_; 
lean_dec_ref(v_indConsts_673_);
v___x_684_ = 0;
return v___x_684_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isRec_spec__1___boxed(lean_object* v_indConsts_685_, lean_object* v_as_686_, lean_object* v_i_687_, lean_object* v_stop_688_){
_start:
{
size_t v_i_boxed_689_; size_t v_stop_boxed_690_; uint8_t v_res_691_; lean_object* v_r_692_; 
v_i_boxed_689_ = lean_unbox_usize(v_i_687_);
lean_dec(v_i_687_);
v_stop_boxed_690_ = lean_unbox_usize(v_stop_688_);
lean_dec(v_stop_688_);
v_res_691_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isRec_spec__1(v_indConsts_685_, v_as_686_, v_i_boxed_689_, v_stop_boxed_690_);
lean_dec_ref(v_as_686_);
v_r_692_ = lean_box(v_res_691_);
return v_r_692_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isRec(lean_object* v_indTypes_693_, lean_object* v_indConsts_694_){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_unsigned_to_nat(0u);
v___x_696_ = lean_array_get_size(v_indTypes_693_);
v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_dec_ref(v_indConsts_694_);
return v___x_697_;
}
else
{
if (v___x_697_ == 0)
{
lean_dec_ref(v_indConsts_694_);
return v___x_697_;
}
else
{
size_t v___x_698_; size_t v___x_699_; uint8_t v___x_700_; 
v___x_698_ = ((size_t)0ULL);
v___x_699_ = lean_usize_of_nat(v___x_696_);
v___x_700_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isRec_spec__1(v_indConsts_694_, v_indTypes_693_, v___x_698_, v___x_699_);
return v___x_700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRec___boxed(lean_object* v_indTypes_701_, lean_object* v_indConsts_702_){
_start:
{
uint8_t v_res_703_; lean_object* v_r_704_; 
v_res_703_ = l_Lean4Lean_AddInductive_isRec(v_indTypes_701_, v_indConsts_702_);
lean_dec_ref(v_indTypes_701_);
v_r_704_ = lean_box(v_res_703_);
return v_r_704_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isReflexive_loop(lean_object* v_indConsts_705_, lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 7)
{
lean_object* v_binderType_707_; lean_object* v_body_708_; uint8_t v___y_710_; uint8_t v___x_712_; 
v_binderType_707_ = lean_ctor_get(v_x_706_, 1);
v_body_708_ = lean_ctor_get(v_x_706_, 2);
v___x_712_ = l_Lean_Expr_isForall(v_binderType_707_);
if (v___x_712_ == 0)
{
v___y_710_ = v___x_712_;
goto v___jp_709_;
}
else
{
uint8_t v___x_713_; 
lean_inc_ref(v_indConsts_705_);
v___x_713_ = l_Lean4Lean_AddInductive_hasIndOcc(v_indConsts_705_, v_binderType_707_);
v___y_710_ = v___x_713_;
goto v___jp_709_;
}
v___jp_709_:
{
if (v___y_710_ == 0)
{
v_x_706_ = v_body_708_;
goto _start;
}
else
{
lean_dec_ref(v_indConsts_705_);
return v___y_710_;
}
}
}
else
{
uint8_t v___x_714_; 
lean_dec_ref(v_indConsts_705_);
v___x_714_ = 0;
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isReflexive_loop___boxed(lean_object* v_indConsts_715_, lean_object* v_x_716_){
_start:
{
uint8_t v_res_717_; lean_object* v_r_718_; 
v_res_717_ = l_Lean4Lean_AddInductive_isReflexive_loop(v_indConsts_715_, v_x_716_);
lean_dec_ref(v_x_716_);
v_r_718_ = lean_box(v_res_717_);
return v_r_718_;
}
}
LEAN_EXPORT uint8_t l_List_any___at___00Lean4Lean_AddInductive_isReflexive_spec__0(lean_object* v_indConsts_719_, lean_object* v_x_720_){
_start:
{
if (lean_obj_tag(v_x_720_) == 0)
{
uint8_t v___x_721_; 
lean_dec_ref(v_indConsts_719_);
v___x_721_ = 0;
return v___x_721_;
}
else
{
lean_object* v_head_722_; lean_object* v_tail_723_; lean_object* v_type_724_; uint8_t v___x_725_; 
v_head_722_ = lean_ctor_get(v_x_720_, 0);
v_tail_723_ = lean_ctor_get(v_x_720_, 1);
v_type_724_ = lean_ctor_get(v_head_722_, 1);
lean_inc_ref(v_indConsts_719_);
v___x_725_ = l_Lean4Lean_AddInductive_isReflexive_loop(v_indConsts_719_, v_type_724_);
if (v___x_725_ == 0)
{
v_x_720_ = v_tail_723_;
goto _start;
}
else
{
lean_dec_ref(v_indConsts_719_);
return v___x_725_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_any___at___00Lean4Lean_AddInductive_isReflexive_spec__0___boxed(lean_object* v_indConsts_727_, lean_object* v_x_728_){
_start:
{
uint8_t v_res_729_; lean_object* v_r_730_; 
v_res_729_ = l_List_any___at___00Lean4Lean_AddInductive_isReflexive_spec__0(v_indConsts_727_, v_x_728_);
lean_dec(v_x_728_);
v_r_730_ = lean_box(v_res_729_);
return v_r_730_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isReflexive_spec__1(lean_object* v_indConsts_731_, lean_object* v_as_732_, size_t v_i_733_, size_t v_stop_734_){
_start:
{
uint8_t v___x_735_; 
v___x_735_ = lean_usize_dec_eq(v_i_733_, v_stop_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; lean_object* v_ctors_737_; uint8_t v___x_738_; 
v___x_736_ = lean_array_uget_borrowed(v_as_732_, v_i_733_);
v_ctors_737_ = lean_ctor_get(v___x_736_, 2);
lean_inc_ref(v_indConsts_731_);
v___x_738_ = l_List_any___at___00Lean4Lean_AddInductive_isReflexive_spec__0(v_indConsts_731_, v_ctors_737_);
if (v___x_738_ == 0)
{
size_t v___x_739_; size_t v___x_740_; 
v___x_739_ = ((size_t)1ULL);
v___x_740_ = lean_usize_add(v_i_733_, v___x_739_);
v_i_733_ = v___x_740_;
goto _start;
}
else
{
lean_dec_ref(v_indConsts_731_);
return v___x_738_;
}
}
else
{
uint8_t v___x_742_; 
lean_dec_ref(v_indConsts_731_);
v___x_742_ = 0;
return v___x_742_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isReflexive_spec__1___boxed(lean_object* v_indConsts_743_, lean_object* v_as_744_, lean_object* v_i_745_, lean_object* v_stop_746_){
_start:
{
size_t v_i_boxed_747_; size_t v_stop_boxed_748_; uint8_t v_res_749_; lean_object* v_r_750_; 
v_i_boxed_747_ = lean_unbox_usize(v_i_745_);
lean_dec(v_i_745_);
v_stop_boxed_748_ = lean_unbox_usize(v_stop_746_);
lean_dec(v_stop_746_);
v_res_749_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isReflexive_spec__1(v_indConsts_743_, v_as_744_, v_i_boxed_747_, v_stop_boxed_748_);
lean_dec_ref(v_as_744_);
v_r_750_ = lean_box(v_res_749_);
return v_r_750_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isReflexive(lean_object* v_indTypes_751_, lean_object* v_indConsts_752_){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_array_get_size(v_indTypes_751_);
v___x_755_ = lean_nat_dec_lt(v___x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_dec_ref(v_indConsts_752_);
return v___x_755_;
}
else
{
if (v___x_755_ == 0)
{
lean_dec_ref(v_indConsts_752_);
return v___x_755_;
}
else
{
size_t v___x_756_; size_t v___x_757_; uint8_t v___x_758_; 
v___x_756_ = ((size_t)0ULL);
v___x_757_ = lean_usize_of_nat(v___x_754_);
v___x_758_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isReflexive_spec__1(v_indConsts_752_, v_indTypes_751_, v___x_756_, v___x_757_);
return v___x_758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isReflexive___boxed(lean_object* v_indTypes_759_, lean_object* v_indConsts_760_){
_start:
{
uint8_t v_res_761_; lean_object* v_r_762_; 
v_res_761_ = l_Lean4Lean_AddInductive_isReflexive(v_indTypes_759_, v_indConsts_760_);
lean_dec_ref(v_indTypes_759_);
v_r_762_ = lean_box(v_res_761_);
return v_r_762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__0(size_t v_sz_763_, size_t v_i_764_, lean_object* v_bs_765_){
_start:
{
uint8_t v___x_766_; 
v___x_766_ = lean_usize_dec_lt(v_i_764_, v_sz_763_);
if (v___x_766_ == 0)
{
return v_bs_765_;
}
else
{
lean_object* v_v_767_; lean_object* v_name_768_; lean_object* v___x_769_; lean_object* v_bs_x27_770_; size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v_v_767_ = lean_array_uget_borrowed(v_bs_765_, v_i_764_);
v_name_768_ = lean_ctor_get(v_v_767_, 0);
lean_inc(v_name_768_);
v___x_769_ = lean_unsigned_to_nat(0u);
v_bs_x27_770_ = lean_array_uset(v_bs_765_, v_i_764_, v___x_769_);
v___x_771_ = ((size_t)1ULL);
v___x_772_ = lean_usize_add(v_i_764_, v___x_771_);
v___x_773_ = lean_array_uset(v_bs_x27_770_, v_i_764_, v_name_768_);
v_i_764_ = v___x_772_;
v_bs_765_ = v___x_773_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__0___boxed(lean_object* v_sz_775_, lean_object* v_i_776_, lean_object* v_bs_777_){
_start:
{
size_t v_sz_boxed_778_; size_t v_i_boxed_779_; lean_object* v_res_780_; 
v_sz_boxed_778_ = lean_unbox_usize(v_sz_775_);
lean_dec(v_sz_775_);
v_i_boxed_779_ = lean_unbox_usize(v_i_776_);
lean_dec(v_i_776_);
v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__0(v_sz_boxed_778_, v_i_boxed_779_, v_bs_777_);
return v_res_780_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__3(lean_object* v_c_781_, lean_object* v_as_782_, size_t v_i_783_, size_t v_stop_784_, lean_object* v_b_785_){
_start:
{
uint8_t v___x_786_; 
v___x_786_ = lean_usize_dec_eq(v_i_783_, v_stop_784_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v_toConstantVal_788_; lean_object* v_name_789_; uint8_t v_allowPrimitive_790_; lean_object* v___x_791_; 
v___x_787_ = lean_array_uget_borrowed(v_as_782_, v_i_783_);
v_toConstantVal_788_ = lean_ctor_get(v___x_787_, 0);
v_name_789_ = lean_ctor_get(v_toConstantVal_788_, 0);
v_allowPrimitive_790_ = lean_ctor_get_uint8(v_c_781_, sizeof(void*)*4 + 1);
lean_inc(v_name_789_);
lean_inc_ref(v_b_785_);
v___x_791_ = l_Lean_Kernel_Environment_checkName(v_b_785_, v_name_789_, v_allowPrimitive_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v_b_785_);
v_a_792_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_791_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_791_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; size_t v___x_802_; size_t v___x_803_; 
lean_dec_ref(v___x_791_);
lean_inc(v___x_787_);
v___x_800_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_800_, 0, v___x_787_);
v___x_801_ = lean_environment_add(v_b_785_, v___x_800_);
v___x_802_ = ((size_t)1ULL);
v___x_803_ = lean_usize_add(v_i_783_, v___x_802_);
v_i_783_ = v___x_803_;
v_b_785_ = v___x_801_;
goto _start;
}
}
else
{
lean_object* v___x_805_; 
v___x_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_805_, 0, v_b_785_);
return v___x_805_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__3___boxed(lean_object* v_c_806_, lean_object* v_as_807_, lean_object* v_i_808_, lean_object* v_stop_809_, lean_object* v_b_810_){
_start:
{
size_t v_i_boxed_811_; size_t v_stop_boxed_812_; lean_object* v_res_813_; 
v_i_boxed_811_ = lean_unbox_usize(v_i_808_);
lean_dec(v_i_808_);
v_stop_boxed_812_ = lean_unbox_usize(v_stop_809_);
lean_dec(v_stop_809_);
v_res_813_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__3(v_c_806_, v_as_807_, v_i_boxed_811_, v_stop_boxed_812_, v_b_810_);
lean_dec_ref(v_as_807_);
lean_dec_ref(v_c_806_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__1(lean_object* v_a_814_, lean_object* v_a_815_){
_start:
{
if (lean_obj_tag(v_a_814_) == 0)
{
lean_object* v___x_816_; 
v___x_816_ = l_List_reverse___redArg(v_a_815_);
return v___x_816_;
}
else
{
lean_object* v_head_817_; lean_object* v_tail_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_827_; 
v_head_817_ = lean_ctor_get(v_a_814_, 0);
v_tail_818_ = lean_ctor_get(v_a_814_, 1);
v_isSharedCheck_827_ = !lean_is_exclusive(v_a_814_);
if (v_isSharedCheck_827_ == 0)
{
v___x_820_ = v_a_814_;
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_tail_818_);
lean_inc(v_head_817_);
lean_dec(v_a_814_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_827_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v_name_822_; lean_object* v___x_824_; 
v_name_822_ = lean_ctor_get(v_head_817_, 0);
lean_inc(v_name_822_);
lean_dec(v_head_817_);
if (v_isShared_821_ == 0)
{
lean_ctor_set(v___x_820_, 1, v_a_815_);
lean_ctor_set(v___x_820_, 0, v_name_822_);
v___x_824_ = v___x_820_;
goto v_reusejp_823_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_name_822_);
lean_ctor_set(v_reuseFailAlloc_826_, 1, v_a_815_);
v___x_824_ = v_reuseFailAlloc_826_;
goto v_reusejp_823_;
}
v_reusejp_823_:
{
v_a_814_ = v_tail_818_;
v_a_815_ = v___x_824_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__2(lean_object* v_c_828_, lean_object* v_stats_829_, lean_object* v_indTypes_830_, lean_object* v_numParams_831_, lean_object* v_all_832_, lean_object* v_numNested_833_, uint8_t v_isUnsafe_834_, lean_object* v_as_835_, lean_object* v_bs_836_, lean_object* v_i_837_, lean_object* v_cs_838_){
_start:
{
lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_839_ = lean_array_get_size(v_as_835_);
v___x_840_ = lean_nat_dec_lt(v_i_837_, v___x_839_);
if (v___x_840_ == 0)
{
lean_dec(v_i_837_);
lean_dec(v_numNested_833_);
lean_dec(v_all_832_);
lean_dec(v_numParams_831_);
lean_dec_ref(v_stats_829_);
return v_cs_838_;
}
else
{
lean_object* v___x_841_; uint8_t v___x_842_; 
v___x_841_ = lean_array_get_size(v_bs_836_);
v___x_842_ = lean_nat_dec_lt(v_i_837_, v___x_841_);
if (v___x_842_ == 0)
{
lean_dec(v_i_837_);
lean_dec(v_numNested_833_);
lean_dec(v_all_832_);
lean_dec(v_numParams_831_);
lean_dec_ref(v_stats_829_);
return v_cs_838_;
}
else
{
lean_object* v_a_843_; lean_object* v_name_844_; lean_object* v_type_845_; lean_object* v_ctors_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_865_; 
v_a_843_ = lean_array_fget(v_as_835_, v_i_837_);
v_name_844_ = lean_ctor_get(v_a_843_, 0);
v_type_845_ = lean_ctor_get(v_a_843_, 1);
v_ctors_846_ = lean_ctor_get(v_a_843_, 2);
v_isSharedCheck_865_ = !lean_is_exclusive(v_a_843_);
if (v_isSharedCheck_865_ == 0)
{
v___x_848_ = v_a_843_;
v_isShared_849_ = v_isSharedCheck_865_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_ctors_846_);
lean_inc(v_type_845_);
lean_inc(v_name_844_);
lean_dec(v_a_843_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_865_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v_lparams_850_; lean_object* v_indConsts_851_; lean_object* v_b_852_; lean_object* v___x_854_; 
v_lparams_850_ = lean_ctor_get(v_c_828_, 2);
v_indConsts_851_ = lean_ctor_get(v_stats_829_, 4);
v_b_852_ = lean_array_fget_borrowed(v_bs_836_, v_i_837_);
lean_inc(v_lparams_850_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 2, v_type_845_);
lean_ctor_set(v___x_848_, 1, v_lparams_850_);
v___x_854_ = v___x_848_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_name_844_);
lean_ctor_set(v_reuseFailAlloc_864_, 1, v_lparams_850_);
lean_ctor_set(v_reuseFailAlloc_864_, 2, v_type_845_);
v___x_854_ = v_reuseFailAlloc_864_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; uint8_t v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; 
v___x_855_ = lean_box(0);
v___x_856_ = l_List_mapTR_loop___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__1(v_ctors_846_, v___x_855_);
lean_inc_ref_n(v_indConsts_851_, 2);
v___x_857_ = l_Lean4Lean_AddInductive_isRec(v_indTypes_830_, v_indConsts_851_);
v___x_858_ = l_Lean4Lean_AddInductive_isReflexive(v_indTypes_830_, v_indConsts_851_);
lean_inc(v_numNested_833_);
lean_inc(v_all_832_);
lean_inc(v_b_852_);
lean_inc(v_numParams_831_);
v___x_859_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v___x_859_, 0, v___x_854_);
lean_ctor_set(v___x_859_, 1, v_numParams_831_);
lean_ctor_set(v___x_859_, 2, v_b_852_);
lean_ctor_set(v___x_859_, 3, v_all_832_);
lean_ctor_set(v___x_859_, 4, v___x_856_);
lean_ctor_set(v___x_859_, 5, v_numNested_833_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*6, v___x_857_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*6 + 1, v_isUnsafe_834_);
lean_ctor_set_uint8(v___x_859_, sizeof(void*)*6 + 2, v___x_858_);
v___x_860_ = lean_unsigned_to_nat(1u);
v___x_861_ = lean_nat_add(v_i_837_, v___x_860_);
lean_dec(v_i_837_);
v___x_862_ = lean_array_push(v_cs_838_, v___x_859_);
v_i_837_ = v___x_861_;
v_cs_838_ = v___x_862_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_zipWithMAux___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__2___boxed(lean_object* v_c_866_, lean_object* v_stats_867_, lean_object* v_indTypes_868_, lean_object* v_numParams_869_, lean_object* v_all_870_, lean_object* v_numNested_871_, lean_object* v_isUnsafe_872_, lean_object* v_as_873_, lean_object* v_bs_874_, lean_object* v_i_875_, lean_object* v_cs_876_){
_start:
{
uint8_t v_isUnsafe_boxed_877_; lean_object* v_res_878_; 
v_isUnsafe_boxed_877_ = lean_unbox(v_isUnsafe_872_);
v_res_878_ = l_Array_zipWithMAux___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__2(v_c_866_, v_stats_867_, v_indTypes_868_, v_numParams_869_, v_all_870_, v_numNested_871_, v_isUnsafe_boxed_877_, v_as_873_, v_bs_874_, v_i_875_, v_cs_876_);
lean_dec_ref(v_bs_874_);
lean_dec_ref(v_as_873_);
lean_dec_ref(v_indTypes_868_);
lean_dec_ref(v_c_866_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareInductiveTypes(lean_object* v_stats_881_, lean_object* v_numParams_882_, lean_object* v_indTypes_883_, lean_object* v_numNested_884_, uint8_t v_isUnsafe_885_, lean_object* v_c_886_){
_start:
{
lean_object* v_nindices_887_; size_t v_sz_888_; size_t v___x_889_; lean_object* v___x_890_; lean_object* v_all_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_infos_894_; lean_object* v_env_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v_nindices_887_ = lean_ctor_get(v_stats_881_, 3);
lean_inc_ref(v_nindices_887_);
v_sz_888_ = lean_array_size(v_indTypes_883_);
v___x_889_ = ((size_t)0ULL);
lean_inc_ref(v_indTypes_883_);
v___x_890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__0(v_sz_888_, v___x_889_, v_indTypes_883_);
v_all_891_ = lean_array_to_list(v___x_890_);
v___x_892_ = lean_unsigned_to_nat(0u);
v___x_893_ = ((lean_object*)(l_Lean4Lean_AddInductive_declareInductiveTypes___closed__0));
v_infos_894_ = l_Array_zipWithMAux___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__2(v_c_886_, v_stats_881_, v_indTypes_883_, v_numParams_882_, v_all_891_, v_numNested_884_, v_isUnsafe_885_, v_indTypes_883_, v_nindices_887_, v___x_892_, v___x_893_);
lean_dec_ref(v_nindices_887_);
lean_dec_ref(v_indTypes_883_);
v_env_895_ = lean_ctor_get(v_c_886_, 0);
v___x_896_ = lean_array_get_size(v_infos_894_);
v___x_897_ = lean_nat_dec_lt(v___x_892_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec_ref(v_infos_894_);
lean_inc_ref(v_env_895_);
v___x_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_898_, 0, v_env_895_);
return v___x_898_;
}
else
{
uint8_t v___x_899_; 
v___x_899_ = lean_nat_dec_le(v___x_896_, v___x_896_);
if (v___x_899_ == 0)
{
if (v___x_897_ == 0)
{
lean_object* v___x_900_; 
lean_dec_ref(v_infos_894_);
lean_inc_ref(v_env_895_);
v___x_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_900_, 0, v_env_895_);
return v___x_900_;
}
else
{
size_t v___x_901_; lean_object* v___x_902_; 
v___x_901_ = lean_usize_of_nat(v___x_896_);
lean_inc_ref(v_env_895_);
v___x_902_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__3(v_c_886_, v_infos_894_, v___x_889_, v___x_901_, v_env_895_);
lean_dec_ref(v_infos_894_);
return v___x_902_;
}
}
else
{
size_t v___x_903_; lean_object* v___x_904_; 
v___x_903_ = lean_usize_of_nat(v___x_896_);
lean_inc_ref(v_env_895_);
v___x_904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__3(v_c_886_, v_infos_894_, v___x_889_, v___x_903_, v_env_895_);
lean_dec_ref(v_infos_894_);
return v___x_904_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareInductiveTypes___boxed(lean_object* v_stats_905_, lean_object* v_numParams_906_, lean_object* v_indTypes_907_, lean_object* v_numNested_908_, lean_object* v_isUnsafe_909_, lean_object* v_c_910_){
_start:
{
uint8_t v_isUnsafe_boxed_911_; lean_object* v_res_912_; 
v_isUnsafe_boxed_911_ = lean_unbox(v_isUnsafe_909_);
v_res_912_ = l_Lean4Lean_AddInductive_declareInductiveTypes(v_stats_905_, v_numParams_906_, v_indTypes_907_, v_numNested_908_, v_isUnsafe_boxed_911_, v_c_910_);
lean_dec_ref(v_c_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg(lean_object* v_args_922_, lean_object* v___x_923_, lean_object* v_range_924_, lean_object* v_b_925_, lean_object* v_i_926_){
_start:
{
lean_object* v_stop_927_; lean_object* v_step_928_; uint8_t v___x_929_; 
v_stop_927_ = lean_ctor_get(v_range_924_, 1);
v_step_928_ = lean_ctor_get(v_range_924_, 2);
v___x_929_ = lean_nat_dec_lt(v_i_926_, v_stop_927_);
if (v___x_929_ == 0)
{
lean_dec(v_i_926_);
lean_dec_ref(v___x_923_);
lean_inc_ref(v_b_925_);
return v_b_925_;
}
else
{
lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_930_ = l_Lean_instInhabitedExpr;
v___x_931_ = lean_array_get_borrowed(v___x_930_, v_args_922_, v_i_926_);
lean_inc_ref(v___x_923_);
v___x_932_ = l_Lean4Lean_AddInductive_hasIndOcc(v___x_923_, v___x_931_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; lean_object* v___x_934_; 
v___x_933_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__0));
v___x_934_ = lean_nat_add(v_i_926_, v_step_928_);
lean_dec(v_i_926_);
v_b_925_ = v___x_933_;
v_i_926_ = v___x_934_;
goto _start;
}
else
{
lean_object* v___x_936_; 
lean_dec(v_i_926_);
lean_dec_ref(v___x_923_);
v___x_936_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__2));
return v___x_936_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___boxed(lean_object* v_args_937_, lean_object* v___x_938_, lean_object* v_range_939_, lean_object* v_b_940_, lean_object* v_i_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg(v_args_937_, v___x_938_, v_range_939_, v_b_940_, v_i_941_);
lean_dec_ref(v_b_940_);
lean_dec_ref(v_range_939_);
lean_dec_ref(v_args_937_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___redArg(lean_object* v___x_943_, lean_object* v_args_944_, lean_object* v_range_945_, lean_object* v_b_946_, lean_object* v_i_947_){
_start:
{
lean_object* v_stop_948_; lean_object* v_step_949_; uint8_t v___x_950_; 
v_stop_948_ = lean_ctor_get(v_range_945_, 1);
v_step_949_ = lean_ctor_get(v_range_945_, 2);
v___x_950_ = lean_nat_dec_lt(v_i_947_, v_stop_948_);
if (v___x_950_ == 0)
{
lean_dec(v_i_947_);
lean_inc_ref(v_b_946_);
return v_b_946_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
v___x_951_ = l_Lean_instInhabitedExpr;
v___x_952_ = lean_box(0);
v___x_953_ = lean_array_get_borrowed(v___x_951_, v___x_943_, v_i_947_);
v___x_954_ = lean_array_get_borrowed(v___x_951_, v_args_944_, v_i_947_);
v___x_955_ = lean_expr_eqv(v___x_953_, v___x_954_);
if (v___x_955_ == 0)
{
lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; 
lean_dec(v_i_947_);
v___x_956_ = lean_box(v___x_955_);
v___x_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_957_, 0, v___x_956_);
v___x_958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_957_);
lean_ctor_set(v___x_958_, 1, v___x_952_);
return v___x_958_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_959_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__0));
v___x_960_ = lean_nat_add(v_i_947_, v_step_949_);
lean_dec(v_i_947_);
v_b_946_ = v___x_959_;
v_i_947_ = v___x_960_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___redArg___boxed(lean_object* v___x_962_, lean_object* v_args_963_, lean_object* v_range_964_, lean_object* v_b_965_, lean_object* v_i_966_){
_start:
{
lean_object* v_res_967_; 
v_res_967_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___redArg(v___x_962_, v_args_963_, v_range_964_, v_b_965_, v_i_966_);
lean_dec_ref(v_b_965_);
lean_dec_ref(v_range_964_);
lean_dec_ref(v_args_963_);
lean_dec_ref(v___x_962_);
return v_res_967_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__2(lean_object* v_stats_968_, lean_object* v_i_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
if (lean_obj_tag(v_x_970_) == 5)
{
lean_object* v_fn_973_; lean_object* v_arg_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; 
v_fn_973_ = lean_ctor_get(v_x_970_, 0);
lean_inc_ref(v_fn_973_);
v_arg_974_ = lean_ctor_get(v_x_970_, 1);
lean_inc_ref(v_arg_974_);
lean_dec_ref(v_x_970_);
v___x_975_ = lean_array_set(v_x_971_, v_x_972_, v_arg_974_);
v___x_976_ = lean_unsigned_to_nat(1u);
v___x_977_ = lean_nat_sub(v_x_972_, v___x_976_);
lean_dec(v_x_972_);
v_x_970_ = v_fn_973_;
v_x_971_ = v___x_975_;
v_x_972_ = v___x_977_;
goto _start;
}
else
{
lean_object* v_nindices_979_; lean_object* v_indConsts_980_; lean_object* v_params_981_; uint8_t v___y_983_; lean_object* v___x_999_; lean_object* v___x_1000_; uint8_t v___x_1001_; 
lean_dec(v_x_972_);
v_nindices_979_ = lean_ctor_get(v_stats_968_, 3);
lean_inc_ref(v_nindices_979_);
v_indConsts_980_ = lean_ctor_get(v_stats_968_, 4);
lean_inc_ref(v_indConsts_980_);
v_params_981_ = lean_ctor_get(v_stats_968_, 5);
lean_inc_ref(v_params_981_);
lean_dec_ref(v_stats_968_);
v___x_999_ = l_Lean_instInhabitedExpr;
v___x_1000_ = lean_array_get_borrowed(v___x_999_, v_indConsts_980_, v_i_969_);
v___x_1001_ = lean_expr_eqv(v_x_970_, v___x_1000_);
lean_dec_ref(v_x_970_);
if (v___x_1001_ == 0)
{
lean_dec_ref(v_nindices_979_);
v___y_983_ = v___x_1001_;
goto v___jp_982_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; uint8_t v___x_1007_; 
v___x_1002_ = lean_unsigned_to_nat(0u);
v___x_1003_ = lean_array_get_size(v_x_971_);
v___x_1004_ = lean_array_get_size(v_params_981_);
v___x_1005_ = lean_array_get(v___x_1002_, v_nindices_979_, v_i_969_);
lean_dec_ref(v_nindices_979_);
v___x_1006_ = lean_nat_add(v___x_1004_, v___x_1005_);
lean_dec(v___x_1005_);
v___x_1007_ = lean_nat_dec_eq(v___x_1003_, v___x_1006_);
lean_dec(v___x_1006_);
v___y_983_ = v___x_1007_;
goto v___jp_982_;
}
v___jp_982_:
{
if (v___y_983_ == 0)
{
lean_dec_ref(v_params_981_);
lean_dec_ref(v_indConsts_980_);
lean_dec_ref(v_x_971_);
return v___y_983_;
}
else
{
lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v_fst_990_; 
v___x_984_ = lean_unsigned_to_nat(0u);
v___x_985_ = lean_array_get_size(v_params_981_);
v___x_986_ = lean_unsigned_to_nat(1u);
v___x_987_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_987_, 0, v___x_984_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
lean_ctor_set(v___x_987_, 2, v___x_986_);
v___x_988_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg___closed__0));
v___x_989_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___redArg(v_params_981_, v_x_971_, v___x_987_, v___x_988_, v___x_984_);
lean_dec_ref(v___x_987_);
lean_dec_ref(v_params_981_);
v_fst_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc(v_fst_990_);
lean_dec_ref(v___x_989_);
if (lean_obj_tag(v_fst_990_) == 0)
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v_fst_994_; 
v___x_991_ = lean_array_get_size(v_x_971_);
v___x_992_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_985_);
lean_ctor_set(v___x_992_, 1, v___x_991_);
lean_ctor_set(v___x_992_, 2, v___x_986_);
v___x_993_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg(v_x_971_, v_indConsts_980_, v___x_992_, v___x_988_, v___x_985_);
lean_dec_ref(v___x_992_);
lean_dec_ref(v_x_971_);
v_fst_994_ = lean_ctor_get(v___x_993_, 0);
lean_inc(v_fst_994_);
lean_dec_ref(v___x_993_);
if (lean_obj_tag(v_fst_994_) == 0)
{
return v___y_983_;
}
else
{
lean_object* v_val_995_; uint8_t v___x_996_; 
v_val_995_ = lean_ctor_get(v_fst_994_, 0);
lean_inc(v_val_995_);
lean_dec_ref(v_fst_994_);
v___x_996_ = lean_unbox(v_val_995_);
lean_dec(v_val_995_);
return v___x_996_;
}
}
else
{
lean_object* v_val_997_; uint8_t v___x_998_; 
lean_dec_ref(v_indConsts_980_);
lean_dec_ref(v_x_971_);
v_val_997_ = lean_ctor_get(v_fst_990_, 0);
lean_inc(v_val_997_);
lean_dec_ref(v_fst_990_);
v___x_998_ = lean_unbox(v_val_997_);
lean_dec(v_val_997_);
return v___x_998_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__2___boxed(lean_object* v_stats_1008_, lean_object* v_i_1009_, lean_object* v_x_1010_, lean_object* v_x_1011_, lean_object* v_x_1012_){
_start:
{
uint8_t v_res_1013_; lean_object* v_r_1014_; 
v_res_1013_ = l_Lean_Expr_withAppAux___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__2(v_stats_1008_, v_i_1009_, v_x_1010_, v_x_1011_, v_x_1012_);
lean_dec(v_i_1009_);
v_r_1014_ = lean_box(v_res_1013_);
return v_r_1014_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0(void){
_start:
{
lean_object* v___x_1015_; lean_object* v_dummy_1016_; 
v___x_1015_ = lean_box(0);
v_dummy_1016_ = l_Lean_Expr_sort___override(v___x_1015_);
return v_dummy_1016_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isValidIndAppIdx(lean_object* v_stats_1017_, lean_object* v_t_1018_, lean_object* v_i_1019_){
_start:
{
lean_object* v_dummy_1020_; lean_object* v_nargs_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v_dummy_1020_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
v_nargs_1021_ = l_Lean_Expr_getAppNumArgs(v_t_1018_);
lean_inc(v_nargs_1021_);
v___x_1022_ = lean_mk_array(v_nargs_1021_, v_dummy_1020_);
v___x_1023_ = lean_unsigned_to_nat(1u);
v___x_1024_ = lean_nat_sub(v_nargs_1021_, v___x_1023_);
lean_dec(v_nargs_1021_);
v___x_1025_ = l_Lean_Expr_withAppAux___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__2(v_stats_1017_, v_i_1019_, v_t_1018_, v___x_1022_, v___x_1024_);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isValidIndAppIdx___boxed(lean_object* v_stats_1026_, lean_object* v_t_1027_, lean_object* v_i_1028_){
_start:
{
uint8_t v_res_1029_; lean_object* v_r_1030_; 
v_res_1029_ = l_Lean4Lean_AddInductive_isValidIndAppIdx(v_stats_1026_, v_t_1027_, v_i_1028_);
lean_dec(v_i_1028_);
v_r_1030_ = lean_box(v_res_1029_);
return v_r_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0(lean_object* v___x_1031_, lean_object* v_args_1032_, lean_object* v_range_1033_, lean_object* v_b_1034_, lean_object* v_i_1035_, lean_object* v_hs_1036_, lean_object* v_hl_1037_){
_start:
{
lean_object* v___x_1038_; 
v___x_1038_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___redArg(v___x_1031_, v_args_1032_, v_range_1033_, v_b_1034_, v_i_1035_);
return v___x_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0___boxed(lean_object* v___x_1039_, lean_object* v_args_1040_, lean_object* v_range_1041_, lean_object* v_b_1042_, lean_object* v_i_1043_, lean_object* v_hs_1044_, lean_object* v_hl_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__0(v___x_1039_, v_args_1040_, v_range_1041_, v_b_1042_, v_i_1043_, v_hs_1044_, v_hl_1045_);
lean_dec_ref(v_b_1042_);
lean_dec_ref(v_range_1041_);
lean_dec_ref(v_args_1040_);
lean_dec_ref(v___x_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1(lean_object* v_args_1047_, lean_object* v___x_1048_, lean_object* v_range_1049_, lean_object* v_b_1050_, lean_object* v_i_1051_, lean_object* v_hs_1052_, lean_object* v_hl_1053_){
_start:
{
lean_object* v___x_1054_; 
v___x_1054_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___redArg(v_args_1047_, v___x_1048_, v_range_1049_, v_b_1050_, v_i_1051_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1___boxed(lean_object* v_args_1055_, lean_object* v___x_1056_, lean_object* v_range_1057_, lean_object* v_b_1058_, lean_object* v_i_1059_, lean_object* v_hs_1060_, lean_object* v_hl_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndAppIdx_spec__1(v_args_1055_, v___x_1056_, v_range_1057_, v_b_1058_, v_i_1059_, v_hs_1060_, v_hl_1061_);
lean_dec_ref(v_b_1058_);
lean_dec_ref(v_range_1057_);
lean_dec_ref(v_args_1055_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg(lean_object* v_stats_1066_, lean_object* v_t_1067_, lean_object* v_range_1068_, lean_object* v_b_1069_, lean_object* v_i_1070_){
_start:
{
lean_object* v_stop_1071_; lean_object* v_step_1072_; uint8_t v___x_1073_; 
v_stop_1071_ = lean_ctor_get(v_range_1068_, 1);
v_step_1072_ = lean_ctor_get(v_range_1068_, 2);
v___x_1073_ = lean_nat_dec_lt(v_i_1070_, v_stop_1071_);
if (v___x_1073_ == 0)
{
lean_object* v___x_1074_; 
lean_dec(v_i_1070_);
lean_dec_ref(v_t_1067_);
lean_dec_ref(v_stats_1066_);
v___x_1074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1074_, 0, v_b_1069_);
return v___x_1074_;
}
else
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
lean_dec_ref(v_b_1069_);
v___x_1075_ = lean_box(0);
lean_inc_ref(v_t_1067_);
lean_inc_ref(v_stats_1066_);
v___x_1076_ = l_Lean4Lean_AddInductive_isValidIndAppIdx(v_stats_1066_, v_t_1067_, v_i_1070_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg___closed__0));
v___x_1078_ = lean_nat_add(v_i_1070_, v_step_1072_);
lean_dec(v_i_1070_);
v_b_1069_ = v___x_1077_;
v_i_1070_ = v___x_1078_;
goto _start;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
lean_dec_ref(v_t_1067_);
lean_dec_ref(v_stats_1066_);
v___x_1080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1080_, 0, v_i_1070_);
v___x_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1081_, 0, v___x_1080_);
lean_ctor_set(v___x_1081_, 1, v___x_1075_);
v___x_1082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg___boxed(lean_object* v_stats_1083_, lean_object* v_t_1084_, lean_object* v_range_1085_, lean_object* v_b_1086_, lean_object* v_i_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg(v_stats_1083_, v_t_1084_, v_range_1085_, v_b_1086_, v_i_1087_);
lean_dec_ref(v_range_1085_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isValidIndApp_x3f(lean_object* v_stats_1089_, lean_object* v_t_1090_){
_start:
{
lean_object* v_indConsts_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v_val_1099_; lean_object* v_fst_1100_; 
v_indConsts_1091_ = lean_ctor_get(v_stats_1089_, 4);
v___x_1092_ = lean_unsigned_to_nat(0u);
v___x_1093_ = lean_array_get_size(v_indConsts_1091_);
v___x_1094_ = lean_unsigned_to_nat(1u);
v___x_1095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1092_);
lean_ctor_set(v___x_1095_, 1, v___x_1093_);
lean_ctor_set(v___x_1095_, 2, v___x_1094_);
v___x_1096_ = lean_box(0);
v___x_1097_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg___closed__0));
v___x_1098_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg(v_stats_1089_, v_t_1090_, v___x_1095_, v___x_1097_, v___x_1092_);
lean_dec_ref(v___x_1095_);
v_val_1099_ = lean_ctor_get(v___x_1098_, 0);
lean_inc(v_val_1099_);
lean_dec(v___x_1098_);
v_fst_1100_ = lean_ctor_get(v_val_1099_, 0);
lean_inc(v_fst_1100_);
lean_dec(v_val_1099_);
if (lean_obj_tag(v_fst_1100_) == 0)
{
return v___x_1096_;
}
else
{
return v_fst_1100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0(lean_object* v_stats_1101_, lean_object* v_t_1102_, lean_object* v_range_1103_, lean_object* v_b_1104_, lean_object* v_i_1105_, lean_object* v_hs_1106_, lean_object* v_hl_1107_){
_start:
{
lean_object* v___x_1108_; 
v___x_1108_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___redArg(v_stats_1101_, v_t_1102_, v_range_1103_, v_b_1104_, v_i_1105_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0___boxed(lean_object* v_stats_1109_, lean_object* v_t_1110_, lean_object* v_range_1111_, lean_object* v_b_1112_, lean_object* v_i_1113_, lean_object* v_hs_1114_, lean_object* v_hl_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_isValidIndApp_x3f_spec__0(v_stats_1109_, v_t_1110_, v_range_1111_, v_b_1112_, v_i_1113_, v_hs_1114_, v_hl_1115_);
lean_dec_ref(v_range_1111_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRecArg_loop(lean_object* v_stats_1119_, lean_object* v_t_1120_, lean_object* v_x_1121_, lean_object* v_a_1122_){
_start:
{
lean_object* v_zero_1123_; uint8_t v_isZero_1124_; 
v_zero_1123_ = lean_unsigned_to_nat(0u);
v_isZero_1124_ = lean_nat_dec_eq(v_x_1121_, v_zero_1123_);
if (v_isZero_1124_ == 1)
{
lean_object* v___x_1125_; 
lean_dec_ref(v_a_1122_);
lean_dec(v_x_1121_);
lean_dec_ref(v_t_1120_);
lean_dec_ref(v_stats_1119_);
v___x_1125_ = ((lean_object*)(l_Lean4Lean_AddInductive_isRecArg_loop___closed__0));
return v___x_1125_;
}
else
{
lean_object* v_env_1126_; lean_object* v_lctx_1127_; lean_object* v_lparams_1128_; lean_object* v_ngen_1129_; uint8_t v_safety_1130_; uint8_t v_allowPrimitive_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
v_env_1126_ = lean_ctor_get(v_a_1122_, 0);
lean_inc_ref_n(v_env_1126_, 2);
v_lctx_1127_ = lean_ctor_get(v_a_1122_, 1);
lean_inc_ref_n(v_lctx_1127_, 2);
v_lparams_1128_ = lean_ctor_get(v_a_1122_, 2);
lean_inc_n(v_lparams_1128_, 2);
v_ngen_1129_ = lean_ctor_get(v_a_1122_, 3);
lean_inc_ref(v_ngen_1129_);
v_safety_1130_ = lean_ctor_get_uint8(v_a_1122_, sizeof(void*)*4);
v_allowPrimitive_1131_ = lean_ctor_get_uint8(v_a_1122_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_1122_);
v___x_1132_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_1132_, 0, v_t_1120_);
v___x_1133_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_1126_, v_safety_1130_, v_lctx_1127_, v_lparams_1128_, v___x_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec_ref(v_ngen_1129_);
lean_dec(v_lparams_1128_);
lean_dec_ref(v_lctx_1127_);
lean_dec_ref(v_env_1126_);
lean_dec(v_x_1121_);
lean_dec_ref(v_stats_1119_);
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1133_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_a_1134_);
lean_dec(v___x_1133_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_a_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
else
{
lean_object* v_a_1142_; lean_object* v___x_1144_; uint8_t v_isShared_1145_; uint8_t v_isSharedCheck_1168_; 
v_a_1142_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1144_ = v___x_1133_;
v_isShared_1145_ = v_isSharedCheck_1168_;
goto v_resetjp_1143_;
}
else
{
lean_inc(v_a_1142_);
lean_dec(v___x_1133_);
v___x_1144_ = lean_box(0);
v_isShared_1145_ = v_isSharedCheck_1168_;
goto v_resetjp_1143_;
}
v_resetjp_1143_:
{
if (lean_obj_tag(v_a_1142_) == 7)
{
lean_object* v_binderName_1146_; lean_object* v_binderType_1147_; lean_object* v_body_1148_; uint8_t v_binderInfo_1149_; lean_object* v_namePrefix_1150_; lean_object* v_idx_1151_; lean_object* v_one_1152_; lean_object* v_n_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; 
lean_del_object(v___x_1144_);
v_binderName_1146_ = lean_ctor_get(v_a_1142_, 0);
lean_inc(v_binderName_1146_);
v_binderType_1147_ = lean_ctor_get(v_a_1142_, 1);
lean_inc_ref(v_binderType_1147_);
v_body_1148_ = lean_ctor_get(v_a_1142_, 2);
lean_inc_ref(v_body_1148_);
v_binderInfo_1149_ = lean_ctor_get_uint8(v_a_1142_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_1142_);
v_namePrefix_1150_ = lean_ctor_get(v_ngen_1129_, 0);
lean_inc_n(v_namePrefix_1150_, 2);
v_idx_1151_ = lean_ctor_get(v_ngen_1129_, 1);
lean_inc_n(v_idx_1151_, 2);
lean_dec_ref(v_ngen_1129_);
v_one_1152_ = lean_unsigned_to_nat(1u);
v_n_1153_ = lean_nat_sub(v_x_1121_, v_one_1152_);
lean_dec(v_x_1121_);
v___x_1154_ = lean_expr_consume_type_annotations(v_binderType_1147_);
v___x_1155_ = l_Lean_Name_num___override(v_namePrefix_1150_, v_idx_1151_);
v___x_1156_ = lean_nat_add(v_idx_1151_, v_one_1152_);
lean_dec(v_idx_1151_);
v___x_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1157_, 0, v_namePrefix_1150_);
lean_ctor_set(v___x_1157_, 1, v___x_1156_);
lean_inc(v___x_1155_);
v___x_1158_ = l_Lean_Expr_fvar___override(v___x_1155_);
v___x_1159_ = 0;
v___x_1160_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1127_, v___x_1155_, v_binderName_1146_, v___x_1154_, v_binderInfo_1149_, v___x_1159_);
v___x_1161_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1161_, 0, v_env_1126_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
lean_ctor_set(v___x_1161_, 2, v_lparams_1128_);
lean_ctor_set(v___x_1161_, 3, v___x_1157_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*4, v_safety_1130_);
lean_ctor_set_uint8(v___x_1161_, sizeof(void*)*4 + 1, v_allowPrimitive_1131_);
v___x_1162_ = lean_expr_instantiate1(v_body_1148_, v___x_1158_);
lean_dec_ref(v___x_1158_);
lean_dec_ref(v_body_1148_);
v_t_1120_ = v___x_1162_;
v_x_1121_ = v_n_1153_;
v_a_1122_ = v___x_1161_;
goto _start;
}
else
{
lean_object* v___x_1164_; lean_object* v___x_1166_; 
lean_dec_ref(v_ngen_1129_);
lean_dec(v_lparams_1128_);
lean_dec_ref(v_lctx_1127_);
lean_dec_ref(v_env_1126_);
lean_dec(v_x_1121_);
v___x_1164_ = l_Lean4Lean_AddInductive_isValidIndApp_x3f(v_stats_1119_, v_a_1142_);
if (v_isShared_1145_ == 0)
{
lean_ctor_set(v___x_1144_, 0, v___x_1164_);
v___x_1166_ = v___x_1144_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRecArg(lean_object* v_stats_1169_, lean_object* v_t_1170_, lean_object* v_a_1171_){
_start:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; 
v___x_1172_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v_a_1171_);
v___x_1173_ = l_Lean4Lean_AddInductive_isRecArg_loop(v_stats_1169_, v_t_1170_, v___x_1172_, v_a_1171_);
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isRecArg___boxed(lean_object* v_stats_1174_, lean_object* v_t_1175_, lean_object* v_a_1176_){
_start:
{
lean_object* v_res_1177_; 
v_res_1177_ = l_Lean4Lean_AddInductive_isRecArg(v_stats_1174_, v_t_1175_, v_a_1176_);
lean_dec_ref(v_a_1176_);
return v_res_1177_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop(lean_object* v_stats_1186_, lean_object* v_ctor_1187_, lean_object* v_idx_1188_, lean_object* v_t_1189_, lean_object* v_x_1190_, lean_object* v_a_1191_){
_start:
{
lean_object* v_zero_1192_; uint8_t v_isZero_1193_; 
v_zero_1192_ = lean_unsigned_to_nat(0u);
v_isZero_1193_ = lean_nat_dec_eq(v_x_1190_, v_zero_1192_);
if (v_isZero_1193_ == 1)
{
lean_object* v___x_1194_; 
lean_dec_ref(v_a_1191_);
lean_dec(v_x_1190_);
lean_dec_ref(v_t_1189_);
lean_dec(v_ctor_1187_);
lean_dec_ref(v_stats_1186_);
v___x_1194_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__0));
return v___x_1194_;
}
else
{
lean_object* v_env_1195_; lean_object* v_lctx_1196_; lean_object* v_lparams_1197_; lean_object* v_ngen_1198_; uint8_t v_safety_1199_; uint8_t v_allowPrimitive_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v_env_1195_ = lean_ctor_get(v_a_1191_, 0);
lean_inc_ref_n(v_env_1195_, 2);
v_lctx_1196_ = lean_ctor_get(v_a_1191_, 1);
lean_inc_ref_n(v_lctx_1196_, 2);
v_lparams_1197_ = lean_ctor_get(v_a_1191_, 2);
lean_inc_n(v_lparams_1197_, 2);
v_ngen_1198_ = lean_ctor_get(v_a_1191_, 3);
lean_inc_ref(v_ngen_1198_);
v_safety_1199_ = lean_ctor_get_uint8(v_a_1191_, sizeof(void*)*4);
v_allowPrimitive_1200_ = lean_ctor_get_uint8(v_a_1191_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_1191_);
v___x_1201_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_1201_, 0, v_t_1189_);
v___x_1202_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_1195_, v_safety_1199_, v_lctx_1196_, v_lparams_1197_, v___x_1201_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1205_; uint8_t v_isShared_1206_; uint8_t v_isSharedCheck_1210_; 
lean_dec_ref(v_ngen_1198_);
lean_dec(v_lparams_1197_);
lean_dec_ref(v_lctx_1196_);
lean_dec_ref(v_env_1195_);
lean_dec(v_x_1190_);
lean_dec(v_ctor_1187_);
lean_dec_ref(v_stats_1186_);
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1210_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1210_ == 0)
{
v___x_1205_ = v___x_1202_;
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
else
{
lean_inc(v_a_1203_);
lean_dec(v___x_1202_);
v___x_1205_ = lean_box(0);
v_isShared_1206_ = v_isSharedCheck_1210_;
goto v_resetjp_1204_;
}
v_resetjp_1204_:
{
lean_object* v___x_1208_; 
if (v_isShared_1206_ == 0)
{
v___x_1208_ = v___x_1205_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_a_1203_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v_a_1211_; lean_object* v___x_1213_; uint8_t v_isShared_1214_; uint8_t v_isSharedCheck_1269_; 
v_a_1211_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1213_ = v___x_1202_;
v_isShared_1214_ = v_isSharedCheck_1269_;
goto v_resetjp_1212_;
}
else
{
lean_inc(v_a_1211_);
lean_dec(v___x_1202_);
v___x_1213_ = lean_box(0);
v_isShared_1214_ = v_isSharedCheck_1269_;
goto v_resetjp_1212_;
}
v_resetjp_1212_:
{
lean_object* v_indConsts_1215_; uint8_t v___x_1216_; 
v_indConsts_1215_ = lean_ctor_get(v_stats_1186_, 4);
lean_inc_ref(v_indConsts_1215_);
v___x_1216_ = l_Lean4Lean_AddInductive_hasIndOcc(v_indConsts_1215_, v_a_1211_);
if (v___x_1216_ == 0)
{
lean_object* v___x_1217_; 
lean_del_object(v___x_1213_);
lean_dec(v_a_1211_);
lean_dec_ref(v_ngen_1198_);
lean_dec(v_lparams_1197_);
lean_dec_ref(v_lctx_1196_);
lean_dec_ref(v_env_1195_);
lean_dec(v_x_1190_);
lean_dec(v_ctor_1187_);
lean_dec_ref(v_stats_1186_);
v___x_1217_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__1));
return v___x_1217_;
}
else
{
if (lean_obj_tag(v_a_1211_) == 7)
{
lean_object* v_binderName_1218_; lean_object* v_binderType_1219_; lean_object* v_body_1220_; uint8_t v_binderInfo_1221_; uint8_t v___x_1222_; 
v_binderName_1218_ = lean_ctor_get(v_a_1211_, 0);
lean_inc(v_binderName_1218_);
v_binderType_1219_ = lean_ctor_get(v_a_1211_, 1);
lean_inc_ref(v_binderType_1219_);
v_body_1220_ = lean_ctor_get(v_a_1211_, 2);
lean_inc_ref(v_body_1220_);
v_binderInfo_1221_ = lean_ctor_get_uint8(v_a_1211_, sizeof(void*)*3 + 8);
lean_dec_ref(v_a_1211_);
lean_inc_ref(v_indConsts_1215_);
v___x_1222_ = l_Lean4Lean_AddInductive_hasIndOcc(v_indConsts_1215_, v_binderType_1219_);
if (v___x_1222_ == 0)
{
lean_object* v_namePrefix_1223_; lean_object* v_idx_1224_; lean_object* v_one_1225_; lean_object* v_n_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_del_object(v___x_1213_);
v_namePrefix_1223_ = lean_ctor_get(v_ngen_1198_, 0);
lean_inc_n(v_namePrefix_1223_, 2);
v_idx_1224_ = lean_ctor_get(v_ngen_1198_, 1);
lean_inc_n(v_idx_1224_, 2);
lean_dec_ref(v_ngen_1198_);
v_one_1225_ = lean_unsigned_to_nat(1u);
v_n_1226_ = lean_nat_sub(v_x_1190_, v_one_1225_);
lean_dec(v_x_1190_);
v___x_1227_ = lean_expr_consume_type_annotations(v_binderType_1219_);
v___x_1228_ = l_Lean_Name_num___override(v_namePrefix_1223_, v_idx_1224_);
v___x_1229_ = lean_nat_add(v_idx_1224_, v_one_1225_);
lean_dec(v_idx_1224_);
v___x_1230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1230_, 0, v_namePrefix_1223_);
lean_ctor_set(v___x_1230_, 1, v___x_1229_);
lean_inc(v___x_1228_);
v___x_1231_ = l_Lean_Expr_fvar___override(v___x_1228_);
v___x_1232_ = 0;
v___x_1233_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1196_, v___x_1228_, v_binderName_1218_, v___x_1227_, v_binderInfo_1221_, v___x_1232_);
v___x_1234_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1234_, 0, v_env_1195_);
lean_ctor_set(v___x_1234_, 1, v___x_1233_);
lean_ctor_set(v___x_1234_, 2, v_lparams_1197_);
lean_ctor_set(v___x_1234_, 3, v___x_1230_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*4, v_safety_1199_);
lean_ctor_set_uint8(v___x_1234_, sizeof(void*)*4 + 1, v_allowPrimitive_1200_);
v___x_1235_ = lean_expr_instantiate1(v_body_1220_, v___x_1231_);
lean_dec_ref(v___x_1231_);
lean_dec_ref(v_body_1220_);
v_t_1189_ = v___x_1235_;
v_x_1190_ = v_n_1226_;
v_a_1191_ = v___x_1234_;
goto _start;
}
else
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
lean_dec_ref(v_body_1220_);
lean_dec_ref(v_binderType_1219_);
lean_dec(v_binderName_1218_);
lean_dec_ref(v_ngen_1198_);
lean_dec(v_lparams_1197_);
lean_dec_ref(v_lctx_1196_);
lean_dec_ref(v_env_1195_);
lean_dec(v_x_1190_);
lean_dec_ref(v_stats_1186_);
v___x_1237_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__2));
v___x_1238_ = lean_unsigned_to_nat(1u);
v___x_1239_ = lean_nat_add(v_idx_1188_, v___x_1238_);
v___x_1240_ = l_Nat_reprFast(v___x_1239_);
v___x_1241_ = lean_string_append(v___x_1237_, v___x_1240_);
lean_dec_ref(v___x_1240_);
v___x_1242_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__3));
v___x_1243_ = lean_string_append(v___x_1241_, v___x_1242_);
v___x_1244_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctor_1187_, v___x_1222_);
v___x_1245_ = lean_string_append(v___x_1243_, v___x_1244_);
lean_dec_ref(v___x_1244_);
v___x_1246_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__4));
v___x_1247_ = lean_string_append(v___x_1245_, v___x_1246_);
v___x_1248_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1247_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1248_);
v___x_1250_ = v___x_1213_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1251_; 
v_reuseFailAlloc_1251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1251_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
return v___x_1250_;
}
}
}
else
{
lean_object* v___x_1252_; 
lean_dec_ref(v_ngen_1198_);
lean_dec(v_lparams_1197_);
lean_dec_ref(v_lctx_1196_);
lean_dec_ref(v_env_1195_);
lean_dec(v_x_1190_);
v___x_1252_ = l_Lean4Lean_AddInductive_isValidIndApp_x3f(v_stats_1186_, v_a_1211_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
v___x_1253_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__2));
v___x_1254_ = lean_unsigned_to_nat(1u);
v___x_1255_ = lean_nat_add(v_idx_1188_, v___x_1254_);
v___x_1256_ = l_Nat_reprFast(v___x_1255_);
v___x_1257_ = lean_string_append(v___x_1253_, v___x_1256_);
lean_dec_ref(v___x_1256_);
v___x_1258_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__3));
v___x_1259_ = lean_string_append(v___x_1257_, v___x_1258_);
v___x_1260_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_ctor_1187_, v___x_1216_);
v___x_1261_ = lean_string_append(v___x_1259_, v___x_1260_);
lean_dec_ref(v___x_1260_);
v___x_1262_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__5));
v___x_1263_ = lean_string_append(v___x_1261_, v___x_1262_);
v___x_1264_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
if (v_isShared_1214_ == 0)
{
lean_ctor_set_tag(v___x_1213_, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1264_);
v___x_1266_ = v___x_1213_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
else
{
lean_object* v___x_1268_; 
lean_dec(v___x_1252_);
lean_del_object(v___x_1213_);
lean_dec(v_ctor_1187_);
v___x_1268_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__1));
return v___x_1268_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity_loop___boxed(lean_object* v_stats_1270_, lean_object* v_ctor_1271_, lean_object* v_idx_1272_, lean_object* v_t_1273_, lean_object* v_x_1274_, lean_object* v_a_1275_){
_start:
{
lean_object* v_res_1276_; 
v_res_1276_ = l_Lean4Lean_AddInductive_checkPositivity_loop(v_stats_1270_, v_ctor_1271_, v_idx_1272_, v_t_1273_, v_x_1274_, v_a_1275_);
lean_dec(v_idx_1272_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity(lean_object* v_stats_1277_, lean_object* v_t_1278_, lean_object* v_ctor_1279_, lean_object* v_idx_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v_a_1281_);
v___x_1283_ = l_Lean4Lean_AddInductive_checkPositivity_loop(v_stats_1277_, v_ctor_1279_, v_idx_1280_, v_t_1278_, v___x_1282_, v_a_1281_);
return v___x_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkPositivity___boxed(lean_object* v_stats_1284_, lean_object* v_t_1285_, lean_object* v_ctor_1286_, lean_object* v_idx_1287_, lean_object* v_a_1288_){
_start:
{
lean_object* v_res_1289_; 
v_res_1289_ = l_Lean4Lean_AddInductive_checkPositivity(v_stats_1284_, v_t_1285_, v_ctor_1286_, v_idx_1287_, v_a_1288_);
lean_dec_ref(v_a_1288_);
lean_dec(v_idx_1287_);
return v_res_1289_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop(lean_object* v_stats_1296_, uint8_t v_isUnsafe_1297_, lean_object* v_idx_1298_, lean_object* v_n_1299_, lean_object* v_t_1300_, lean_object* v_i_1301_, lean_object* v_x_1302_, lean_object* v_a_1303_){
_start:
{
lean_object* v_zero_1304_; uint8_t v_isZero_1305_; 
v_zero_1304_ = lean_unsigned_to_nat(0u);
v_isZero_1305_ = lean_nat_dec_eq(v_x_1302_, v_zero_1304_);
if (v_isZero_1305_ == 1)
{
lean_object* v___x_1306_; 
lean_dec_ref(v_a_1303_);
lean_dec(v_x_1302_);
lean_dec(v_i_1301_);
lean_dec_ref(v_t_1300_);
lean_dec(v_n_1299_);
lean_dec_ref(v_stats_1296_);
v___x_1306_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__0));
return v___x_1306_;
}
else
{
if (lean_obj_tag(v_t_1300_) == 7)
{
lean_object* v_binderName_1307_; lean_object* v_binderType_1308_; lean_object* v_body_1309_; uint8_t v_binderInfo_1310_; lean_object* v_resultLevel_1311_; lean_object* v_params_1312_; lean_object* v_one_1313_; lean_object* v_n_1314_; lean_object* v_env_1316_; lean_object* v_lctx_1317_; lean_object* v_lparams_1318_; lean_object* v_ngen_1319_; uint8_t v_safety_1320_; uint8_t v_allowPrimitive_1321_; lean_object* v___x_1335_; uint8_t v___x_1336_; 
v_binderName_1307_ = lean_ctor_get(v_t_1300_, 0);
lean_inc(v_binderName_1307_);
v_binderType_1308_ = lean_ctor_get(v_t_1300_, 1);
lean_inc_ref(v_binderType_1308_);
v_body_1309_ = lean_ctor_get(v_t_1300_, 2);
lean_inc_ref(v_body_1309_);
v_binderInfo_1310_ = lean_ctor_get_uint8(v_t_1300_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_1300_);
v_resultLevel_1311_ = lean_ctor_get(v_stats_1296_, 2);
v_params_1312_ = lean_ctor_get(v_stats_1296_, 5);
v_one_1313_ = lean_unsigned_to_nat(1u);
v_n_1314_ = lean_nat_sub(v_x_1302_, v_one_1313_);
lean_dec(v_x_1302_);
v___x_1335_ = lean_array_get_size(v_params_1312_);
v___x_1336_ = lean_nat_dec_lt(v_i_1301_, v___x_1335_);
if (v___x_1336_ == 0)
{
lean_object* v_env_1337_; lean_object* v_lctx_1338_; lean_object* v_lparams_1339_; lean_object* v_ngen_1340_; uint8_t v_safety_1341_; uint8_t v_allowPrimitive_1342_; uint8_t v___y_1344_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
v_env_1337_ = lean_ctor_get(v_a_1303_, 0);
lean_inc_ref_n(v_env_1337_, 2);
v_lctx_1338_ = lean_ctor_get(v_a_1303_, 1);
lean_inc_ref_n(v_lctx_1338_, 2);
v_lparams_1339_ = lean_ctor_get(v_a_1303_, 2);
lean_inc_n(v_lparams_1339_, 2);
v_ngen_1340_ = lean_ctor_get(v_a_1303_, 3);
lean_inc_ref(v_ngen_1340_);
v_safety_1341_ = lean_ctor_get_uint8(v_a_1303_, sizeof(void*)*4);
v_allowPrimitive_1342_ = lean_ctor_get_uint8(v_a_1303_, sizeof(void*)*4 + 1);
lean_inc_ref(v_binderType_1308_);
v___x_1359_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_ensureType___boxed), 3, 1);
lean_closure_set(v___x_1359_, 0, v_binderType_1308_);
v___x_1360_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_1337_, v_safety_1341_, v_lctx_1338_, v_lparams_1339_, v___x_1359_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1363_; uint8_t v_isShared_1364_; uint8_t v_isSharedCheck_1368_; 
lean_dec_ref(v_ngen_1340_);
lean_dec(v_lparams_1339_);
lean_dec_ref(v_lctx_1338_);
lean_dec_ref(v_env_1337_);
lean_dec(v_n_1314_);
lean_dec_ref(v_body_1309_);
lean_dec_ref(v_binderType_1308_);
lean_dec(v_binderName_1307_);
lean_dec_ref(v_a_1303_);
lean_dec(v_i_1301_);
lean_dec(v_n_1299_);
lean_dec_ref(v_stats_1296_);
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1368_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1368_ == 0)
{
v___x_1363_ = v___x_1360_;
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
else
{
lean_inc(v_a_1361_);
lean_dec(v___x_1360_);
v___x_1363_ = lean_box(0);
v_isShared_1364_ = v_isSharedCheck_1368_;
goto v_resetjp_1362_;
}
v_resetjp_1362_:
{
lean_object* v___x_1366_; 
if (v_isShared_1364_ == 0)
{
v___x_1366_ = v___x_1363_;
goto v_reusejp_1365_;
}
else
{
lean_object* v_reuseFailAlloc_1367_; 
v_reuseFailAlloc_1367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1367_, 0, v_a_1361_);
v___x_1366_ = v_reuseFailAlloc_1367_;
goto v_reusejp_1365_;
}
v_reusejp_1365_:
{
return v___x_1366_;
}
}
}
else
{
lean_object* v_a_1369_; uint8_t v___x_1370_; 
v_a_1369_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1369_);
lean_dec_ref(v___x_1360_);
v___x_1370_ = l_Lean_Level_isZero(v_resultLevel_1311_);
if (v___x_1370_ == 0)
{
lean_object* v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = l_Lean_Expr_sortLevel_x21(v_a_1369_);
lean_dec(v_a_1369_);
lean_inc(v_resultLevel_1311_);
v___x_1372_ = l_Lean_Level_geq_x27(v_resultLevel_1311_, v___x_1371_);
v___y_1344_ = v___x_1372_;
goto v___jp_1343_;
}
else
{
lean_dec(v_a_1369_);
v___y_1344_ = v___x_1370_;
goto v___jp_1343_;
}
}
v___jp_1343_:
{
if (v___y_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
lean_dec_ref(v_ngen_1340_);
lean_dec(v_lparams_1339_);
lean_dec_ref(v_lctx_1338_);
lean_dec_ref(v_env_1337_);
lean_dec(v_n_1314_);
lean_dec_ref(v_body_1309_);
lean_dec_ref(v_binderType_1308_);
lean_dec(v_binderName_1307_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_stats_1296_);
v___x_1345_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkConstructors_loop___closed__0));
v___x_1346_ = lean_nat_add(v_i_1301_, v_one_1313_);
lean_dec(v_i_1301_);
v___x_1347_ = l_Nat_reprFast(v___x_1346_);
v___x_1348_ = lean_string_append(v___x_1345_, v___x_1347_);
lean_dec_ref(v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkConstructors_loop___closed__1));
v___x_1350_ = lean_string_append(v___x_1348_, v___x_1349_);
v___x_1351_ = 1;
v___x_1352_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1299_, v___x_1351_);
v___x_1353_ = lean_string_append(v___x_1350_, v___x_1352_);
lean_dec_ref(v___x_1352_);
v___x_1354_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkConstructors_loop___closed__2));
v___x_1355_ = lean_string_append(v___x_1353_, v___x_1354_);
v___x_1356_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1355_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v___x_1356_);
return v___x_1357_;
}
else
{
if (v_isUnsafe_1297_ == 0)
{
lean_object* v___x_1358_; 
lean_inc(v_n_1299_);
lean_inc_ref(v_binderType_1308_);
lean_inc_ref(v_stats_1296_);
v___x_1358_ = l_Lean4Lean_AddInductive_checkPositivity(v_stats_1296_, v_binderType_1308_, v_n_1299_, v_i_1301_, v_a_1303_);
lean_dec_ref(v_a_1303_);
if (lean_obj_tag(v___x_1358_) == 0)
{
lean_dec_ref(v_ngen_1340_);
lean_dec(v_lparams_1339_);
lean_dec_ref(v_lctx_1338_);
lean_dec_ref(v_env_1337_);
lean_dec(v_n_1314_);
lean_dec_ref(v_body_1309_);
lean_dec_ref(v_binderType_1308_);
lean_dec(v_binderName_1307_);
lean_dec(v_i_1301_);
lean_dec(v_n_1299_);
lean_dec_ref(v_stats_1296_);
return v___x_1358_;
}
else
{
lean_dec_ref(v___x_1358_);
v_env_1316_ = v_env_1337_;
v_lctx_1317_ = v_lctx_1338_;
v_lparams_1318_ = v_lparams_1339_;
v_ngen_1319_ = v_ngen_1340_;
v_safety_1320_ = v_safety_1341_;
v_allowPrimitive_1321_ = v_allowPrimitive_1342_;
goto v___jp_1315_;
}
}
else
{
lean_dec_ref(v_a_1303_);
v_env_1316_ = v_env_1337_;
v_lctx_1317_ = v_lctx_1338_;
v_lparams_1318_ = v_lparams_1339_;
v_ngen_1319_ = v_ngen_1340_;
v_safety_1320_ = v_safety_1341_;
v_allowPrimitive_1321_ = v_allowPrimitive_1342_;
goto v___jp_1315_;
}
}
}
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1418_; 
lean_dec(v_binderName_1307_);
v___x_1373_ = lean_array_fget_borrowed(v_params_1312_, v_i_1301_);
v___x_1374_ = l_Lean4Lean_AddInductive_getType(v___x_1373_, v_a_1303_);
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1418_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1418_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1418_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1418_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v_env_1379_; lean_object* v_lctx_1380_; lean_object* v_lparams_1381_; uint8_t v_safety_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v_env_1379_ = lean_ctor_get(v_a_1303_, 0);
v_lctx_1380_ = lean_ctor_get(v_a_1303_, 1);
v_lparams_1381_ = lean_ctor_get(v_a_1303_, 2);
v_safety_1382_ = lean_ctor_get_uint8(v_a_1303_, sizeof(void*)*4);
v___x_1383_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_isDefEq___boxed), 4, 2);
lean_closure_set(v___x_1383_, 0, v_binderType_1308_);
lean_closure_set(v___x_1383_, 1, v_a_1375_);
lean_inc(v_lparams_1381_);
lean_inc_ref(v_lctx_1380_);
lean_inc_ref(v_env_1379_);
v___x_1384_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_1379_, v_safety_1382_, v_lctx_1380_, v_lparams_1381_, v___x_1383_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; lean_object* v___x_1387_; uint8_t v_isShared_1388_; uint8_t v_isSharedCheck_1392_; 
lean_del_object(v___x_1377_);
lean_dec(v_n_1314_);
lean_dec_ref(v_body_1309_);
lean_dec_ref(v_a_1303_);
lean_dec(v_i_1301_);
lean_dec(v_n_1299_);
lean_dec_ref(v_stats_1296_);
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1392_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1392_ == 0)
{
v___x_1387_ = v___x_1384_;
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
else
{
lean_inc(v_a_1385_);
lean_dec(v___x_1384_);
v___x_1387_ = lean_box(0);
v_isShared_1388_ = v_isSharedCheck_1392_;
goto v_resetjp_1386_;
}
v_resetjp_1386_:
{
lean_object* v___x_1390_; 
if (v_isShared_1388_ == 0)
{
v___x_1390_ = v___x_1387_;
goto v_reusejp_1389_;
}
else
{
lean_object* v_reuseFailAlloc_1391_; 
v_reuseFailAlloc_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1391_, 0, v_a_1385_);
v___x_1390_ = v_reuseFailAlloc_1391_;
goto v_reusejp_1389_;
}
v_reusejp_1389_:
{
return v___x_1390_;
}
}
}
else
{
lean_object* v_a_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1417_; 
v_a_1393_ = lean_ctor_get(v___x_1384_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1384_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1395_ = v___x_1384_;
v_isShared_1396_ = v_isSharedCheck_1417_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_a_1393_);
lean_dec(v___x_1384_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1417_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
uint8_t v___x_1397_; 
v___x_1397_ = lean_unbox(v_a_1393_);
lean_dec(v_a_1393_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1409_; 
lean_dec(v_n_1314_);
lean_dec_ref(v_body_1309_);
lean_dec_ref(v_a_1303_);
lean_dec_ref(v_stats_1296_);
v___x_1398_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__2));
v___x_1399_ = lean_nat_add(v_i_1301_, v_one_1313_);
lean_dec(v_i_1301_);
v___x_1400_ = l_Nat_reprFast(v___x_1399_);
v___x_1401_ = lean_string_append(v___x_1398_, v___x_1400_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__3));
v___x_1403_ = lean_string_append(v___x_1401_, v___x_1402_);
v___x_1404_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1299_, v___x_1336_);
v___x_1405_ = lean_string_append(v___x_1403_, v___x_1404_);
lean_dec_ref(v___x_1404_);
v___x_1406_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkConstructors_loop___closed__3));
v___x_1407_ = lean_string_append(v___x_1405_, v___x_1406_);
if (v_isShared_1378_ == 0)
{
lean_ctor_set_tag(v___x_1377_, 12);
lean_ctor_set(v___x_1377_, 0, v___x_1407_);
v___x_1409_ = v___x_1377_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1407_);
v___x_1409_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
lean_object* v___x_1411_; 
if (v_isShared_1396_ == 0)
{
lean_ctor_set_tag(v___x_1395_, 0);
lean_ctor_set(v___x_1395_, 0, v___x_1409_);
v___x_1411_ = v___x_1395_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1409_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
else
{
lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_del_object(v___x_1395_);
lean_del_object(v___x_1377_);
v___x_1414_ = lean_expr_instantiate1(v_body_1309_, v___x_1373_);
lean_dec_ref(v_body_1309_);
v___x_1415_ = lean_nat_add(v_i_1301_, v_one_1313_);
lean_dec(v_i_1301_);
v_t_1300_ = v___x_1414_;
v_i_1301_ = v___x_1415_;
v_x_1302_ = v_n_1314_;
goto _start;
}
}
}
}
}
v___jp_1315_:
{
lean_object* v_namePrefix_1322_; lean_object* v_idx_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v_namePrefix_1322_ = lean_ctor_get(v_ngen_1319_, 0);
lean_inc_n(v_namePrefix_1322_, 2);
v_idx_1323_ = lean_ctor_get(v_ngen_1319_, 1);
lean_inc_n(v_idx_1323_, 2);
lean_dec_ref(v_ngen_1319_);
v___x_1324_ = lean_expr_consume_type_annotations(v_binderType_1308_);
v___x_1325_ = l_Lean_Name_num___override(v_namePrefix_1322_, v_idx_1323_);
v___x_1326_ = lean_nat_add(v_idx_1323_, v_one_1313_);
lean_dec(v_idx_1323_);
v___x_1327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1327_, 0, v_namePrefix_1322_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
lean_inc(v___x_1325_);
v___x_1328_ = l_Lean_Expr_fvar___override(v___x_1325_);
v___x_1329_ = 0;
v___x_1330_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1317_, v___x_1325_, v_binderName_1307_, v___x_1324_, v_binderInfo_1310_, v___x_1329_);
v___x_1331_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1331_, 0, v_env_1316_);
lean_ctor_set(v___x_1331_, 1, v___x_1330_);
lean_ctor_set(v___x_1331_, 2, v_lparams_1318_);
lean_ctor_set(v___x_1331_, 3, v___x_1327_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*4, v_safety_1320_);
lean_ctor_set_uint8(v___x_1331_, sizeof(void*)*4 + 1, v_allowPrimitive_1321_);
v___x_1332_ = lean_expr_instantiate1(v_body_1309_, v___x_1328_);
lean_dec_ref(v___x_1328_);
lean_dec_ref(v_body_1309_);
v___x_1333_ = lean_nat_add(v_i_1301_, v_one_1313_);
lean_dec(v_i_1301_);
v_t_1300_ = v___x_1332_;
v_i_1301_ = v___x_1333_;
v_x_1302_ = v_n_1314_;
v_a_1303_ = v___x_1331_;
goto _start;
}
}
else
{
uint8_t v___x_1419_; 
lean_dec_ref(v_a_1303_);
lean_dec(v_x_1302_);
lean_dec(v_i_1301_);
v___x_1419_ = l_Lean4Lean_AddInductive_isValidIndAppIdx(v_stats_1296_, v_t_1300_, v_idx_1298_);
if (v___x_1419_ == 0)
{
uint8_t v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1420_ = 1;
v___x_1421_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkConstructors_loop___closed__4));
v___x_1422_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_n_1299_, v___x_1420_);
v___x_1423_ = lean_string_append(v___x_1421_, v___x_1422_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkConstructors_loop___closed__5));
v___x_1425_ = lean_string_append(v___x_1423_, v___x_1424_);
v___x_1426_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1426_, 0, v___x_1425_);
v___x_1427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1426_);
return v___x_1427_;
}
else
{
lean_object* v___x_1428_; 
lean_dec(v_n_1299_);
v___x_1428_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__1));
return v___x_1428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors_loop___boxed(lean_object* v_stats_1429_, lean_object* v_isUnsafe_1430_, lean_object* v_idx_1431_, lean_object* v_n_1432_, lean_object* v_t_1433_, lean_object* v_i_1434_, lean_object* v_x_1435_, lean_object* v_a_1436_){
_start:
{
uint8_t v_isUnsafe_boxed_1437_; lean_object* v_res_1438_; 
v_isUnsafe_boxed_1437_ = lean_unbox(v_isUnsafe_1430_);
v_res_1438_ = l_Lean4Lean_AddInductive_checkConstructors_loop(v_stats_1429_, v_isUnsafe_boxed_1437_, v_idx_1431_, v_n_1432_, v_t_1433_, v_i_1434_, v_x_1435_, v_a_1436_);
lean_dec(v_idx_1431_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg(lean_object* v_a_1440_, lean_object* v_stats_1441_, uint8_t v_isUnsafe_1442_, lean_object* v_idx_1443_, lean_object* v_as_x27_1444_, lean_object* v_b_1445_, lean_object* v___y_1446_){
_start:
{
if (lean_obj_tag(v_as_x27_1444_) == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref(v_stats_1441_);
lean_dec_ref(v_a_1440_);
v___x_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1447_, 0, v_b_1445_);
return v___x_1447_;
}
else
{
lean_object* v_head_1448_; lean_object* v_tail_1449_; lean_object* v_name_1450_; lean_object* v_type_1451_; uint8_t v___x_1452_; 
v_head_1448_ = lean_ctor_get(v_as_x27_1444_, 0);
v_tail_1449_ = lean_ctor_get(v_as_x27_1444_, 1);
v_name_1450_ = lean_ctor_get(v_head_1448_, 0);
v_type_1451_ = lean_ctor_get(v_head_1448_, 1);
v___x_1452_ = l_Lean_NameSet_contains(v_b_1445_, v_name_1450_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
lean_inc_n(v_name_1450_, 2);
v___x_1453_ = l_Lean_NameSet_insert(v_b_1445_, v_name_1450_);
lean_inc_ref(v_type_1451_);
lean_inc_ref(v_a_1440_);
v___x_1454_ = l_Lean_Kernel_Environment_checkNoMVarNoFVar(v_a_1440_, v_name_1450_, v_type_1451_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v_a_1455_; lean_object* v___x_1457_; uint8_t v_isShared_1458_; uint8_t v_isSharedCheck_1462_; 
lean_dec(v___x_1453_);
lean_dec_ref(v_stats_1441_);
lean_dec_ref(v_a_1440_);
v_a_1455_ = lean_ctor_get(v___x_1454_, 0);
v_isSharedCheck_1462_ = !lean_is_exclusive(v___x_1454_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1457_ = v___x_1454_;
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
else
{
lean_inc(v_a_1455_);
lean_dec(v___x_1454_);
v___x_1457_ = lean_box(0);
v_isShared_1458_ = v_isSharedCheck_1462_;
goto v_resetjp_1456_;
}
v_resetjp_1456_:
{
lean_object* v___x_1460_; 
if (v_isShared_1458_ == 0)
{
v___x_1460_ = v___x_1457_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v_a_1455_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
return v___x_1460_;
}
}
}
else
{
lean_object* v_env_1463_; lean_object* v_lctx_1464_; lean_object* v_lparams_1465_; uint8_t v_safety_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
lean_dec_ref(v___x_1454_);
v_env_1463_ = lean_ctor_get(v___y_1446_, 0);
v_lctx_1464_ = lean_ctor_get(v___y_1446_, 1);
v_lparams_1465_ = lean_ctor_get(v___y_1446_, 2);
v_safety_1466_ = lean_ctor_get_uint8(v___y_1446_, sizeof(void*)*4);
lean_inc_ref(v_type_1451_);
v___x_1467_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_checkType___boxed), 3, 1);
lean_closure_set(v___x_1467_, 0, v_type_1451_);
lean_inc(v_lparams_1465_);
lean_inc_ref(v_lctx_1464_);
lean_inc_ref(v_env_1463_);
v___x_1468_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_1463_, v_safety_1466_, v_lctx_1464_, v_lparams_1465_, v___x_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1471_; uint8_t v_isShared_1472_; uint8_t v_isSharedCheck_1476_; 
lean_dec(v___x_1453_);
lean_dec_ref(v_stats_1441_);
lean_dec_ref(v_a_1440_);
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1476_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1476_ == 0)
{
v___x_1471_ = v___x_1468_;
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
else
{
lean_inc(v_a_1469_);
lean_dec(v___x_1468_);
v___x_1471_ = lean_box(0);
v_isShared_1472_ = v_isSharedCheck_1476_;
goto v_resetjp_1470_;
}
v_resetjp_1470_:
{
lean_object* v___x_1474_; 
if (v_isShared_1472_ == 0)
{
v___x_1474_ = v___x_1471_;
goto v_reusejp_1473_;
}
else
{
lean_object* v_reuseFailAlloc_1475_; 
v_reuseFailAlloc_1475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1475_, 0, v_a_1469_);
v___x_1474_ = v_reuseFailAlloc_1475_;
goto v_reusejp_1473_;
}
v_reusejp_1473_:
{
return v___x_1474_;
}
}
}
else
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; 
lean_dec_ref(v___x_1468_);
v___x_1477_ = lean_unsigned_to_nat(0u);
v___x_1478_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v___y_1446_);
lean_inc_ref(v_type_1451_);
lean_inc(v_name_1450_);
lean_inc_ref(v_stats_1441_);
v___x_1479_ = l_Lean4Lean_AddInductive_checkConstructors_loop(v_stats_1441_, v_isUnsafe_1442_, v_idx_1443_, v_name_1450_, v_type_1451_, v___x_1477_, v___x_1478_, v___y_1446_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v___x_1453_);
lean_dec_ref(v_stats_1441_);
lean_dec_ref(v_a_1440_);
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
else
{
lean_dec_ref(v___x_1479_);
v_as_x27_1444_ = v_tail_1449_;
v_b_1445_ = v___x_1453_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec(v_b_1445_);
lean_dec_ref(v_stats_1441_);
lean_dec_ref(v_a_1440_);
v___x_1489_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg___closed__0));
lean_inc(v_name_1450_);
v___x_1490_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_name_1450_, v___x_1452_);
v___x_1491_ = lean_string_append(v___x_1489_, v___x_1490_);
lean_dec_ref(v___x_1490_);
v___x_1492_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkConstructors_loop___closed__5));
v___x_1493_ = lean_string_append(v___x_1491_, v___x_1492_);
v___x_1494_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
return v___x_1495_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg___boxed(lean_object* v_a_1496_, lean_object* v_stats_1497_, lean_object* v_isUnsafe_1498_, lean_object* v_idx_1499_, lean_object* v_as_x27_1500_, lean_object* v_b_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_isUnsafe_boxed_1503_; lean_object* v_res_1504_; 
v_isUnsafe_boxed_1503_ = lean_unbox(v_isUnsafe_1498_);
v_res_1504_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg(v_a_1496_, v_stats_1497_, v_isUnsafe_boxed_1503_, v_idx_1499_, v_as_x27_1500_, v_b_1501_, v___y_1502_);
lean_dec_ref(v___y_1502_);
lean_dec(v_as_x27_1500_);
lean_dec(v_idx_1499_);
return v_res_1504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___redArg(lean_object* v_indTypes_1505_, lean_object* v_a_1506_, lean_object* v_stats_1507_, uint8_t v_isUnsafe_1508_, lean_object* v_range_1509_, lean_object* v_b_1510_, lean_object* v_i_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_stop_1513_; lean_object* v_step_1514_; uint8_t v___x_1515_; 
v_stop_1513_ = lean_ctor_get(v_range_1509_, 1);
v_step_1514_ = lean_ctor_get(v_range_1509_, 2);
v___x_1515_ = lean_nat_dec_lt(v_i_1511_, v_stop_1513_);
if (v___x_1515_ == 0)
{
lean_object* v___x_1516_; 
lean_dec(v_i_1511_);
lean_dec_ref(v_stats_1507_);
lean_dec_ref(v_a_1506_);
v___x_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1516_, 0, v_b_1510_);
return v___x_1516_;
}
else
{
lean_object* v___x_1517_; lean_object* v_ctors_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1517_ = lean_array_fget_borrowed(v_indTypes_1505_, v_i_1511_);
v_ctors_1518_ = lean_ctor_get(v___x_1517_, 2);
v___x_1519_ = l_Lean_NameSet_empty;
lean_inc_ref(v_stats_1507_);
lean_inc_ref(v_a_1506_);
v___x_1520_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg(v_a_1506_, v_stats_1507_, v_isUnsafe_1508_, v_i_1511_, v_ctors_1518_, v___x_1519_, v___y_1512_);
if (lean_obj_tag(v___x_1520_) == 0)
{
lean_object* v_a_1521_; lean_object* v___x_1523_; uint8_t v_isShared_1524_; uint8_t v_isSharedCheck_1528_; 
lean_dec(v_i_1511_);
lean_dec_ref(v_stats_1507_);
lean_dec_ref(v_a_1506_);
v_a_1521_ = lean_ctor_get(v___x_1520_, 0);
v_isSharedCheck_1528_ = !lean_is_exclusive(v___x_1520_);
if (v_isSharedCheck_1528_ == 0)
{
v___x_1523_ = v___x_1520_;
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
else
{
lean_inc(v_a_1521_);
lean_dec(v___x_1520_);
v___x_1523_ = lean_box(0);
v_isShared_1524_ = v_isSharedCheck_1528_;
goto v_resetjp_1522_;
}
v_resetjp_1522_:
{
lean_object* v___x_1526_; 
if (v_isShared_1524_ == 0)
{
v___x_1526_ = v___x_1523_;
goto v_reusejp_1525_;
}
else
{
lean_object* v_reuseFailAlloc_1527_; 
v_reuseFailAlloc_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1527_, 0, v_a_1521_);
v___x_1526_ = v_reuseFailAlloc_1527_;
goto v_reusejp_1525_;
}
v_reusejp_1525_:
{
return v___x_1526_;
}
}
}
else
{
lean_object* v___x_1529_; lean_object* v___x_1530_; 
lean_dec_ref(v___x_1520_);
v___x_1529_ = lean_box(0);
v___x_1530_ = lean_nat_add(v_i_1511_, v_step_1514_);
lean_dec(v_i_1511_);
v_b_1510_ = v___x_1529_;
v_i_1511_ = v___x_1530_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___redArg___boxed(lean_object* v_indTypes_1532_, lean_object* v_a_1533_, lean_object* v_stats_1534_, lean_object* v_isUnsafe_1535_, lean_object* v_range_1536_, lean_object* v_b_1537_, lean_object* v_i_1538_, lean_object* v___y_1539_){
_start:
{
uint8_t v_isUnsafe_boxed_1540_; lean_object* v_res_1541_; 
v_isUnsafe_boxed_1540_ = lean_unbox(v_isUnsafe_1535_);
v_res_1541_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___redArg(v_indTypes_1532_, v_a_1533_, v_stats_1534_, v_isUnsafe_boxed_1540_, v_range_1536_, v_b_1537_, v_i_1538_, v___y_1539_);
lean_dec_ref(v___y_1539_);
lean_dec_ref(v_range_1536_);
lean_dec_ref(v_indTypes_1532_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___redArg(lean_object* v_a_1542_, lean_object* v_stats_1543_, uint8_t v_isUnsafe_1544_, lean_object* v_indTypes_1545_, lean_object* v_range_1546_, lean_object* v_b_1547_, lean_object* v_i_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v_stop_1550_; lean_object* v_step_1551_; uint8_t v___x_1552_; 
v_stop_1550_ = lean_ctor_get(v_range_1546_, 1);
v_step_1551_ = lean_ctor_get(v_range_1546_, 2);
v___x_1552_ = lean_nat_dec_lt(v_i_1548_, v_stop_1550_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; 
lean_dec_ref(v_stats_1543_);
lean_dec_ref(v_a_1542_);
v___x_1553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1553_, 0, v_b_1547_);
return v___x_1553_;
}
else
{
lean_object* v___x_1554_; lean_object* v_ctors_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1554_ = lean_array_fget_borrowed(v_indTypes_1545_, v_i_1548_);
v_ctors_1555_ = lean_ctor_get(v___x_1554_, 2);
v___x_1556_ = l_Lean_NameSet_empty;
lean_inc_ref(v_stats_1543_);
lean_inc_ref(v_a_1542_);
v___x_1557_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg(v_a_1542_, v_stats_1543_, v_isUnsafe_1544_, v_i_1548_, v_ctors_1555_, v___x_1556_, v___y_1549_);
if (lean_obj_tag(v___x_1557_) == 0)
{
lean_object* v_a_1558_; lean_object* v___x_1560_; uint8_t v_isShared_1561_; uint8_t v_isSharedCheck_1565_; 
lean_dec_ref(v_stats_1543_);
lean_dec_ref(v_a_1542_);
v_a_1558_ = lean_ctor_get(v___x_1557_, 0);
v_isSharedCheck_1565_ = !lean_is_exclusive(v___x_1557_);
if (v_isSharedCheck_1565_ == 0)
{
v___x_1560_ = v___x_1557_;
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
else
{
lean_inc(v_a_1558_);
lean_dec(v___x_1557_);
v___x_1560_ = lean_box(0);
v_isShared_1561_ = v_isSharedCheck_1565_;
goto v_resetjp_1559_;
}
v_resetjp_1559_:
{
lean_object* v___x_1563_; 
if (v_isShared_1561_ == 0)
{
v___x_1563_ = v___x_1560_;
goto v_reusejp_1562_;
}
else
{
lean_object* v_reuseFailAlloc_1564_; 
v_reuseFailAlloc_1564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1564_, 0, v_a_1558_);
v___x_1563_ = v_reuseFailAlloc_1564_;
goto v_reusejp_1562_;
}
v_reusejp_1562_:
{
return v___x_1563_;
}
}
}
else
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec_ref(v___x_1557_);
v___x_1566_ = lean_box(0);
v___x_1567_ = lean_nat_add(v_i_1548_, v_step_1551_);
v___x_1568_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___redArg(v_indTypes_1545_, v_a_1542_, v_stats_1543_, v_isUnsafe_1544_, v_range_1546_, v___x_1566_, v___x_1567_, v___y_1549_);
return v___x_1568_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___redArg___boxed(lean_object* v_a_1569_, lean_object* v_stats_1570_, lean_object* v_isUnsafe_1571_, lean_object* v_indTypes_1572_, lean_object* v_range_1573_, lean_object* v_b_1574_, lean_object* v_i_1575_, lean_object* v___y_1576_){
_start:
{
uint8_t v_isUnsafe_boxed_1577_; lean_object* v_res_1578_; 
v_isUnsafe_boxed_1577_ = lean_unbox(v_isUnsafe_1571_);
v_res_1578_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___redArg(v_a_1569_, v_stats_1570_, v_isUnsafe_boxed_1577_, v_indTypes_1572_, v_range_1573_, v_b_1574_, v_i_1575_, v___y_1576_);
lean_dec_ref(v___y_1576_);
lean_dec(v_i_1575_);
lean_dec_ref(v_range_1573_);
lean_dec_ref(v_indTypes_1572_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors(lean_object* v_indTypes_1579_, lean_object* v_stats_1580_, uint8_t v_isUnsafe_1581_, lean_object* v_a_1582_){
_start:
{
lean_object* v_env_1583_; lean_object* v_lctx_1584_; lean_object* v_lparams_1585_; uint8_t v_safety_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v_env_1583_ = lean_ctor_get(v_a_1582_, 0);
v_lctx_1584_ = lean_ctor_get(v_a_1582_, 1);
v_lparams_1585_ = lean_ctor_get(v_a_1582_, 2);
v_safety_1586_ = lean_ctor_get_uint8(v_a_1582_, sizeof(void*)*4);
v___x_1587_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_getEnv___boxed), 2, 0);
lean_inc(v_lparams_1585_);
lean_inc_ref(v_lctx_1584_);
lean_inc_ref(v_env_1583_);
v___x_1588_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_1583_, v_safety_1586_, v_lctx_1584_, v_lparams_1585_, v___x_1587_);
if (lean_obj_tag(v___x_1588_) == 0)
{
lean_object* v_a_1589_; lean_object* v___x_1591_; uint8_t v_isShared_1592_; uint8_t v_isSharedCheck_1596_; 
lean_dec_ref(v_stats_1580_);
v_a_1589_ = lean_ctor_get(v___x_1588_, 0);
v_isSharedCheck_1596_ = !lean_is_exclusive(v___x_1588_);
if (v_isSharedCheck_1596_ == 0)
{
v___x_1591_ = v___x_1588_;
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
else
{
lean_inc(v_a_1589_);
lean_dec(v___x_1588_);
v___x_1591_ = lean_box(0);
v_isShared_1592_ = v_isSharedCheck_1596_;
goto v_resetjp_1590_;
}
v_resetjp_1590_:
{
lean_object* v___x_1594_; 
if (v_isShared_1592_ == 0)
{
v___x_1594_ = v___x_1591_;
goto v_reusejp_1593_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_a_1589_);
v___x_1594_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1593_;
}
v_reusejp_1593_:
{
return v___x_1594_;
}
}
}
else
{
lean_object* v_a_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1603_; 
v_a_1597_ = lean_ctor_get(v___x_1588_, 0);
lean_inc(v_a_1597_);
lean_dec_ref(v___x_1588_);
v___x_1598_ = lean_unsigned_to_nat(0u);
v___x_1599_ = lean_array_get_size(v_indTypes_1579_);
v___x_1600_ = lean_unsigned_to_nat(1u);
v___x_1601_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1598_);
lean_ctor_set(v___x_1601_, 1, v___x_1599_);
lean_ctor_set(v___x_1601_, 2, v___x_1600_);
v___x_1602_ = lean_box(0);
v___x_1603_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___redArg(v_a_1597_, v_stats_1580_, v_isUnsafe_1581_, v_indTypes_1579_, v___x_1601_, v___x_1602_, v___x_1598_, v_a_1582_);
lean_dec_ref(v___x_1601_);
if (lean_obj_tag(v___x_1603_) == 0)
{
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; 
lean_dec_ref(v___x_1603_);
v___x_1604_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkPositivity_loop___closed__1));
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_checkConstructors___boxed(lean_object* v_indTypes_1605_, lean_object* v_stats_1606_, lean_object* v_isUnsafe_1607_, lean_object* v_a_1608_){
_start:
{
uint8_t v_isUnsafe_boxed_1609_; lean_object* v_res_1610_; 
v_isUnsafe_boxed_1609_ = lean_unbox(v_isUnsafe_1607_);
v_res_1610_ = l_Lean4Lean_AddInductive_checkConstructors(v_indTypes_1605_, v_stats_1606_, v_isUnsafe_boxed_1609_, v_a_1608_);
lean_dec_ref(v_a_1608_);
lean_dec_ref(v_indTypes_1605_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0(lean_object* v_a_1611_, lean_object* v_stats_1612_, uint8_t v_isUnsafe_1613_, lean_object* v_idx_1614_, lean_object* v_as_1615_, lean_object* v_as_x27_1616_, lean_object* v_b_1617_, lean_object* v_a_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___redArg(v_a_1611_, v_stats_1612_, v_isUnsafe_1613_, v_idx_1614_, v_as_x27_1616_, v_b_1617_, v___y_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0___boxed(lean_object* v_a_1621_, lean_object* v_stats_1622_, lean_object* v_isUnsafe_1623_, lean_object* v_idx_1624_, lean_object* v_as_1625_, lean_object* v_as_x27_1626_, lean_object* v_b_1627_, lean_object* v_a_1628_, lean_object* v___y_1629_){
_start:
{
uint8_t v_isUnsafe_boxed_1630_; lean_object* v_res_1631_; 
v_isUnsafe_boxed_1630_ = lean_unbox(v_isUnsafe_1623_);
v_res_1631_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__0(v_a_1621_, v_stats_1622_, v_isUnsafe_boxed_1630_, v_idx_1624_, v_as_1625_, v_as_x27_1626_, v_b_1627_, v_a_1628_, v___y_1629_);
lean_dec_ref(v___y_1629_);
lean_dec(v_as_x27_1626_);
lean_dec(v_as_1625_);
lean_dec(v_idx_1624_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1(lean_object* v_a_1632_, lean_object* v_stats_1633_, uint8_t v_isUnsafe_1634_, lean_object* v_indTypes_1635_, lean_object* v_range_1636_, lean_object* v_b_1637_, lean_object* v_i_1638_, lean_object* v_hs_1639_, lean_object* v_hl_1640_, lean_object* v___y_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___redArg(v_a_1632_, v_stats_1633_, v_isUnsafe_1634_, v_indTypes_1635_, v_range_1636_, v_b_1637_, v_i_1638_, v___y_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1___boxed(lean_object* v_a_1643_, lean_object* v_stats_1644_, lean_object* v_isUnsafe_1645_, lean_object* v_indTypes_1646_, lean_object* v_range_1647_, lean_object* v_b_1648_, lean_object* v_i_1649_, lean_object* v_hs_1650_, lean_object* v_hl_1651_, lean_object* v___y_1652_){
_start:
{
uint8_t v_isUnsafe_boxed_1653_; lean_object* v_res_1654_; 
v_isUnsafe_boxed_1653_ = lean_unbox(v_isUnsafe_1645_);
v_res_1654_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1(v_a_1643_, v_stats_1644_, v_isUnsafe_boxed_1653_, v_indTypes_1646_, v_range_1647_, v_b_1648_, v_i_1649_, v_hs_1650_, v_hl_1651_, v___y_1652_);
lean_dec_ref(v___y_1652_);
lean_dec(v_i_1649_);
lean_dec_ref(v_range_1647_);
lean_dec_ref(v_indTypes_1646_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1(lean_object* v_indTypes_1655_, lean_object* v_a_1656_, lean_object* v_stats_1657_, uint8_t v_isUnsafe_1658_, lean_object* v_range_1659_, lean_object* v_b_1660_, lean_object* v_i_1661_, lean_object* v_hs_1662_, lean_object* v_hl_1663_, lean_object* v___y_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___redArg(v_indTypes_1655_, v_a_1656_, v_stats_1657_, v_isUnsafe_1658_, v_range_1659_, v_b_1660_, v_i_1661_, v___y_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1___boxed(lean_object* v_indTypes_1666_, lean_object* v_a_1667_, lean_object* v_stats_1668_, lean_object* v_isUnsafe_1669_, lean_object* v_range_1670_, lean_object* v_b_1671_, lean_object* v_i_1672_, lean_object* v_hs_1673_, lean_object* v_hl_1674_, lean_object* v___y_1675_){
_start:
{
uint8_t v_isUnsafe_boxed_1676_; lean_object* v_res_1677_; 
v_isUnsafe_boxed_1676_ = lean_unbox(v_isUnsafe_1669_);
v_res_1677_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00__private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_checkConstructors_spec__1_spec__1(v_indTypes_1666_, v_a_1667_, v_stats_1668_, v_isUnsafe_boxed_1676_, v_range_1670_, v_b_1671_, v_i_1672_, v_hs_1673_, v_hl_1674_, v___y_1675_);
lean_dec_ref(v___y_1675_);
lean_dec_ref(v_range_1670_);
lean_dec_ref(v_indTypes_1666_);
return v_res_1677_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors_arity(lean_object* v_i_1678_, lean_object* v_x_1679_){
_start:
{
if (lean_obj_tag(v_x_1679_) == 7)
{
lean_object* v_body_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; 
v_body_1680_ = lean_ctor_get(v_x_1679_, 2);
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_add(v_i_1678_, v___x_1681_);
lean_dec(v_i_1678_);
v_i_1678_ = v___x_1682_;
v_x_1679_ = v_body_1680_;
goto _start;
}
else
{
return v_i_1678_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors_arity___boxed(lean_object* v_i_1684_, lean_object* v_x_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_Lean4Lean_AddInductive_declareConstructors_arity(v_i_1684_, v_x_1685_);
lean_dec_ref(v_x_1685_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_AddInductive_declareConstructors_spec__0(lean_object* v_msg_1687_){
_start:
{
lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1688_ = lean_unsigned_to_nat(0u);
v___x_1689_ = lean_panic_fn_borrowed(v___x_1688_, v_msg_1687_);
return v___x_1689_;
}
}
static lean_object* _init_l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__2(void){
_start:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1692_ = ((lean_object*)(l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__1));
v___x_1693_ = lean_unsigned_to_nat(21u);
v___x_1694_ = lean_unsigned_to_nat(252u);
v___x_1695_ = ((lean_object*)(l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__0));
v___x_1696_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_1697_ = l_mkPanicMessageWithDecl(v___x_1696_, v___x_1695_, v___x_1694_, v___x_1693_, v___x_1692_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1(lean_object* v_c_1698_, lean_object* v_indType_1699_, lean_object* v_stats_1700_, uint8_t v_isUnsafe_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_){
_start:
{
if (lean_obj_tag(v_x_1703_) == 0)
{
lean_object* v___x_1704_; 
v___x_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1704_, 0, v_x_1702_);
return v___x_1704_;
}
else
{
lean_object* v_head_1705_; lean_object* v_tail_1706_; lean_object* v_fst_1707_; lean_object* v_snd_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1746_; 
v_head_1705_ = lean_ctor_get(v_x_1703_, 0);
lean_inc(v_head_1705_);
v_tail_1706_ = lean_ctor_get(v_x_1703_, 1);
lean_inc(v_tail_1706_);
lean_dec_ref(v_x_1703_);
v_fst_1707_ = lean_ctor_get(v_x_1702_, 0);
v_snd_1708_ = lean_ctor_get(v_x_1702_, 1);
v_isSharedCheck_1746_ = !lean_is_exclusive(v_x_1702_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1710_ = v_x_1702_;
v_isShared_1711_ = v_isSharedCheck_1746_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_snd_1708_);
lean_inc(v_fst_1707_);
lean_dec(v_x_1702_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1746_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v_name_1712_; lean_object* v_type_1713_; lean_object* v_lparams_1714_; uint8_t v_allowPrimitive_1715_; lean_object* v___x_1716_; 
v_name_1712_ = lean_ctor_get(v_head_1705_, 0);
lean_inc_n(v_name_1712_, 2);
v_type_1713_ = lean_ctor_get(v_head_1705_, 1);
lean_inc_ref(v_type_1713_);
lean_dec(v_head_1705_);
v_lparams_1714_ = lean_ctor_get(v_c_1698_, 2);
v_allowPrimitive_1715_ = lean_ctor_get_uint8(v_c_1698_, sizeof(void*)*4 + 1);
lean_inc(v_snd_1708_);
v___x_1716_ = l_Lean_Kernel_Environment_checkName(v_snd_1708_, v_name_1712_, v_allowPrimitive_1715_);
if (lean_obj_tag(v___x_1716_) == 0)
{
lean_object* v_a_1717_; lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1724_; 
lean_dec_ref(v_type_1713_);
lean_dec(v_name_1712_);
lean_del_object(v___x_1710_);
lean_dec(v_snd_1708_);
lean_dec(v_fst_1707_);
lean_dec(v_tail_1706_);
v_a_1717_ = lean_ctor_get(v___x_1716_, 0);
v_isSharedCheck_1724_ = !lean_is_exclusive(v___x_1716_);
if (v_isSharedCheck_1724_ == 0)
{
v___x_1719_ = v___x_1716_;
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
else
{
lean_inc(v_a_1717_);
lean_dec(v___x_1716_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1724_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v___x_1722_; 
if (v_isShared_1720_ == 0)
{
v___x_1722_ = v___x_1719_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v_a_1717_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
}
else
{
lean_object* v_name_1725_; lean_object* v_params_1726_; lean_object* v___x_1727_; lean_object* v_arity_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___y_1734_; uint8_t v___x_1742_; 
lean_dec_ref(v___x_1716_);
v_name_1725_ = lean_ctor_get(v_indType_1699_, 0);
v_params_1726_ = lean_ctor_get(v_stats_1700_, 5);
v___x_1727_ = lean_unsigned_to_nat(0u);
v_arity_1728_ = l_Lean4Lean_AddInductive_declareConstructors_arity(v___x_1727_, v_type_1713_);
v___x_1729_ = lean_unsigned_to_nat(1u);
v___x_1730_ = lean_nat_add(v_fst_1707_, v___x_1729_);
lean_inc(v_lparams_1714_);
v___x_1731_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1731_, 0, v_name_1712_);
lean_ctor_set(v___x_1731_, 1, v_lparams_1714_);
lean_ctor_set(v___x_1731_, 2, v_type_1713_);
v___x_1732_ = lean_array_get_size(v_params_1726_);
v___x_1742_ = lean_nat_dec_le(v___x_1732_, v_arity_1728_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1744_; 
lean_dec(v_arity_1728_);
v___x_1743_ = lean_obj_once(&l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__2, &l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__2_once, _init_l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___closed__2);
v___x_1744_ = l_panic___at___00Lean4Lean_AddInductive_declareConstructors_spec__0(v___x_1743_);
v___y_1734_ = v___x_1744_;
goto v___jp_1733_;
}
else
{
lean_object* v___x_1745_; 
v___x_1745_ = lean_nat_sub(v_arity_1728_, v___x_1732_);
lean_dec(v_arity_1728_);
v___y_1734_ = v___x_1745_;
goto v___jp_1733_;
}
v___jp_1733_:
{
lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1739_; 
lean_inc(v_name_1725_);
v___x_1735_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1735_, 0, v___x_1731_);
lean_ctor_set(v___x_1735_, 1, v_name_1725_);
lean_ctor_set(v___x_1735_, 2, v_fst_1707_);
lean_ctor_set(v___x_1735_, 3, v___x_1732_);
lean_ctor_set(v___x_1735_, 4, v___y_1734_);
lean_ctor_set_uint8(v___x_1735_, sizeof(void*)*5, v_isUnsafe_1701_);
v___x_1736_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
v___x_1737_ = lean_environment_add(v_snd_1708_, v___x_1736_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 1, v___x_1737_);
lean_ctor_set(v___x_1710_, 0, v___x_1730_);
v___x_1739_ = v___x_1710_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v___x_1730_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v___x_1737_);
v___x_1739_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
v_x_1702_ = v___x_1739_;
v_x_1703_ = v_tail_1706_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1___boxed(lean_object* v_c_1747_, lean_object* v_indType_1748_, lean_object* v_stats_1749_, lean_object* v_isUnsafe_1750_, lean_object* v_x_1751_, lean_object* v_x_1752_){
_start:
{
uint8_t v_isUnsafe_boxed_1753_; lean_object* v_res_1754_; 
v_isUnsafe_boxed_1753_ = lean_unbox(v_isUnsafe_1750_);
v_res_1754_ = l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1(v_c_1747_, v_indType_1748_, v_stats_1749_, v_isUnsafe_boxed_1753_, v_x_1751_, v_x_1752_);
lean_dec_ref(v_stats_1749_);
lean_dec_ref(v_indType_1748_);
lean_dec_ref(v_c_1747_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareConstructors_spec__2(lean_object* v_c_1755_, lean_object* v_stats_1756_, uint8_t v_isUnsafe_1757_, lean_object* v_as_1758_, size_t v_i_1759_, size_t v_stop_1760_, lean_object* v_b_1761_){
_start:
{
uint8_t v___x_1762_; 
v___x_1762_ = lean_usize_dec_eq(v_i_1759_, v_stop_1760_);
if (v___x_1762_ == 0)
{
lean_object* v___x_1763_; lean_object* v_ctors_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1763_ = lean_array_uget_borrowed(v_as_1758_, v_i_1759_);
v_ctors_1764_ = lean_ctor_get(v___x_1763_, 2);
v___x_1765_ = lean_unsigned_to_nat(0u);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___x_1765_);
lean_ctor_set(v___x_1766_, 1, v_b_1761_);
lean_inc(v_ctors_1764_);
v___x_1767_ = l_List_foldlM___at___00Lean4Lean_AddInductive_declareConstructors_spec__1(v_c_1755_, v___x_1763_, v_stats_1756_, v_isUnsafe_1757_, v___x_1766_, v_ctors_1764_);
if (lean_obj_tag(v___x_1767_) == 0)
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
v_a_1768_ = lean_ctor_get(v___x_1767_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1767_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1767_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
else
{
lean_object* v_a_1776_; lean_object* v_snd_1777_; size_t v___x_1778_; size_t v___x_1779_; 
v_a_1776_ = lean_ctor_get(v___x_1767_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1767_);
v_snd_1777_ = lean_ctor_get(v_a_1776_, 1);
lean_inc(v_snd_1777_);
lean_dec(v_a_1776_);
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_add(v_i_1759_, v___x_1778_);
v_i_1759_ = v___x_1779_;
v_b_1761_ = v_snd_1777_;
goto _start;
}
}
else
{
lean_object* v___x_1781_; 
v___x_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1781_, 0, v_b_1761_);
return v___x_1781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareConstructors_spec__2___boxed(lean_object* v_c_1782_, lean_object* v_stats_1783_, lean_object* v_isUnsafe_1784_, lean_object* v_as_1785_, lean_object* v_i_1786_, lean_object* v_stop_1787_, lean_object* v_b_1788_){
_start:
{
uint8_t v_isUnsafe_boxed_1789_; size_t v_i_boxed_1790_; size_t v_stop_boxed_1791_; lean_object* v_res_1792_; 
v_isUnsafe_boxed_1789_ = lean_unbox(v_isUnsafe_1784_);
v_i_boxed_1790_ = lean_unbox_usize(v_i_1786_);
lean_dec(v_i_1786_);
v_stop_boxed_1791_ = lean_unbox_usize(v_stop_1787_);
lean_dec(v_stop_1787_);
v_res_1792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareConstructors_spec__2(v_c_1782_, v_stats_1783_, v_isUnsafe_boxed_1789_, v_as_1785_, v_i_boxed_1790_, v_stop_boxed_1791_, v_b_1788_);
lean_dec_ref(v_as_1785_);
lean_dec_ref(v_stats_1783_);
lean_dec_ref(v_c_1782_);
return v_res_1792_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors(lean_object* v_stats_1793_, lean_object* v_indTypes_1794_, uint8_t v_isUnsafe_1795_, lean_object* v_c_1796_){
_start:
{
lean_object* v_env_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; uint8_t v___x_1800_; 
v_env_1797_ = lean_ctor_get(v_c_1796_, 0);
v___x_1798_ = lean_unsigned_to_nat(0u);
v___x_1799_ = lean_array_get_size(v_indTypes_1794_);
v___x_1800_ = lean_nat_dec_lt(v___x_1798_, v___x_1799_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
lean_inc_ref(v_env_1797_);
v___x_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1801_, 0, v_env_1797_);
return v___x_1801_;
}
else
{
uint8_t v___x_1802_; 
v___x_1802_ = lean_nat_dec_le(v___x_1799_, v___x_1799_);
if (v___x_1802_ == 0)
{
if (v___x_1800_ == 0)
{
lean_object* v___x_1803_; 
lean_inc_ref(v_env_1797_);
v___x_1803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1803_, 0, v_env_1797_);
return v___x_1803_;
}
else
{
size_t v___x_1804_; size_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = ((size_t)0ULL);
v___x_1805_ = lean_usize_of_nat(v___x_1799_);
lean_inc_ref(v_env_1797_);
v___x_1806_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareConstructors_spec__2(v_c_1796_, v_stats_1793_, v_isUnsafe_1795_, v_indTypes_1794_, v___x_1804_, v___x_1805_, v_env_1797_);
return v___x_1806_;
}
}
else
{
size_t v___x_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = ((size_t)0ULL);
v___x_1808_ = lean_usize_of_nat(v___x_1799_);
lean_inc_ref(v_env_1797_);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_declareConstructors_spec__2(v_c_1796_, v_stats_1793_, v_isUnsafe_1795_, v_indTypes_1794_, v___x_1807_, v___x_1808_, v_env_1797_);
return v___x_1809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_declareConstructors___boxed(lean_object* v_stats_1810_, lean_object* v_indTypes_1811_, lean_object* v_isUnsafe_1812_, lean_object* v_c_1813_){
_start:
{
uint8_t v_isUnsafe_boxed_1814_; lean_object* v_res_1815_; 
v_isUnsafe_boxed_1814_ = lean_unbox(v_isUnsafe_1812_);
v_res_1815_ = l_Lean4Lean_AddInductive_declareConstructors(v_stats_1810_, v_indTypes_1811_, v_isUnsafe_boxed_1814_, v_c_1813_);
lean_dec_ref(v_c_1813_);
lean_dec_ref(v_indTypes_1811_);
lean_dec_ref(v_stats_1810_);
return v_res_1815_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0_spec__0(lean_object* v_a_1816_, lean_object* v_as_1817_, size_t v_i_1818_, size_t v_stop_1819_){
_start:
{
uint8_t v___x_1820_; 
v___x_1820_ = lean_usize_dec_eq(v_i_1818_, v_stop_1819_);
if (v___x_1820_ == 0)
{
lean_object* v___x_1821_; uint8_t v___x_1822_; 
v___x_1821_ = lean_array_uget_borrowed(v_as_1817_, v_i_1818_);
v___x_1822_ = lean_expr_eqv(v_a_1816_, v___x_1821_);
if (v___x_1822_ == 0)
{
size_t v___x_1823_; size_t v___x_1824_; 
v___x_1823_ = ((size_t)1ULL);
v___x_1824_ = lean_usize_add(v_i_1818_, v___x_1823_);
v_i_1818_ = v___x_1824_;
goto _start;
}
else
{
return v___x_1822_;
}
}
else
{
uint8_t v___x_1826_; 
v___x_1826_ = 0;
return v___x_1826_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0_spec__0___boxed(lean_object* v_a_1827_, lean_object* v_as_1828_, lean_object* v_i_1829_, lean_object* v_stop_1830_){
_start:
{
size_t v_i_boxed_1831_; size_t v_stop_boxed_1832_; uint8_t v_res_1833_; lean_object* v_r_1834_; 
v_i_boxed_1831_ = lean_unbox_usize(v_i_1829_);
lean_dec(v_i_1829_);
v_stop_boxed_1832_ = lean_unbox_usize(v_stop_1830_);
lean_dec(v_stop_1830_);
v_res_1833_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0_spec__0(v_a_1827_, v_as_1828_, v_i_boxed_1831_, v_stop_boxed_1832_);
lean_dec_ref(v_as_1828_);
lean_dec_ref(v_a_1827_);
v_r_1834_ = lean_box(v_res_1833_);
return v_r_1834_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0(lean_object* v_as_1835_, lean_object* v_a_1836_){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; uint8_t v___x_1839_; 
v___x_1837_ = lean_unsigned_to_nat(0u);
v___x_1838_ = lean_array_get_size(v_as_1835_);
v___x_1839_ = lean_nat_dec_lt(v___x_1837_, v___x_1838_);
if (v___x_1839_ == 0)
{
return v___x_1839_;
}
else
{
if (v___x_1839_ == 0)
{
return v___x_1839_;
}
else
{
size_t v___x_1840_; size_t v___x_1841_; uint8_t v___x_1842_; 
v___x_1840_ = ((size_t)0ULL);
v___x_1841_ = lean_usize_of_nat(v___x_1838_);
v___x_1842_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0_spec__0(v_a_1836_, v_as_1835_, v___x_1840_, v___x_1841_);
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0___boxed(lean_object* v_as_1843_, lean_object* v_a_1844_){
_start:
{
uint8_t v_res_1845_; lean_object* v_r_1846_; 
v_res_1845_ = l_Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0(v_as_1843_, v_a_1844_);
lean_dec_ref(v_a_1844_);
lean_dec_ref(v_as_1843_);
v_r_1846_ = lean_box(v_res_1845_);
return v_r_1846_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__1(lean_object* v___x_1847_, lean_object* v_as_1848_, size_t v_i_1849_, size_t v_stop_1850_){
_start:
{
uint8_t v___x_1851_; 
v___x_1851_ = lean_usize_dec_eq(v_i_1849_, v_stop_1850_);
if (v___x_1851_ == 0)
{
uint8_t v___x_1852_; lean_object* v___x_1853_; uint8_t v___x_1854_; 
v___x_1852_ = 1;
v___x_1853_ = lean_array_uget_borrowed(v_as_1848_, v_i_1849_);
v___x_1854_ = l_Array_contains___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__0(v___x_1847_, v___x_1853_);
if (v___x_1854_ == 0)
{
return v___x_1852_;
}
else
{
if (v___x_1851_ == 0)
{
size_t v___x_1855_; size_t v___x_1856_; 
v___x_1855_ = ((size_t)1ULL);
v___x_1856_ = lean_usize_add(v_i_1849_, v___x_1855_);
v_i_1849_ = v___x_1856_;
goto _start;
}
else
{
return v___x_1852_;
}
}
}
else
{
uint8_t v___x_1858_; 
v___x_1858_ = 0;
return v___x_1858_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__1___boxed(lean_object* v___x_1859_, lean_object* v_as_1860_, lean_object* v_i_1861_, lean_object* v_stop_1862_){
_start:
{
size_t v_i_boxed_1863_; size_t v_stop_boxed_1864_; uint8_t v_res_1865_; lean_object* v_r_1866_; 
v_i_boxed_1863_ = lean_unbox_usize(v_i_1861_);
lean_dec(v_i_1861_);
v_stop_boxed_1864_ = lean_unbox_usize(v_stop_1862_);
lean_dec(v_stop_1862_);
v_res_1865_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__1(v___x_1859_, v_as_1860_, v_i_boxed_1863_, v_stop_boxed_1864_);
lean_dec_ref(v_as_1860_);
lean_dec_ref(v___x_1859_);
v_r_1866_ = lean_box(v_res_1865_);
return v_r_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator_loop(lean_object* v_stats_1872_, lean_object* v_type_1873_, lean_object* v_i_1874_, lean_object* v_toCheck_1875_, lean_object* v_x_1876_, lean_object* v_a_1877_){
_start:
{
lean_object* v_zero_1878_; uint8_t v_isZero_1879_; 
v_zero_1878_ = lean_unsigned_to_nat(0u);
v_isZero_1879_ = lean_nat_dec_eq(v_x_1876_, v_zero_1878_);
if (v_isZero_1879_ == 1)
{
lean_object* v___x_1880_; 
lean_dec_ref(v_a_1877_);
lean_dec(v_x_1876_);
lean_dec_ref(v_toCheck_1875_);
lean_dec(v_i_1874_);
lean_dec_ref(v_type_1873_);
v___x_1880_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__0));
return v___x_1880_;
}
else
{
if (lean_obj_tag(v_type_1873_) == 7)
{
lean_object* v_ngen_1881_; lean_object* v_binderName_1882_; lean_object* v_binderType_1883_; lean_object* v_body_1884_; uint8_t v_binderInfo_1885_; lean_object* v_env_1886_; lean_object* v_lctx_1887_; lean_object* v_lparams_1888_; uint8_t v_safety_1889_; uint8_t v_allowPrimitive_1890_; lean_object* v_namePrefix_1891_; lean_object* v_idx_1892_; lean_object* v_params_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v_one_1896_; lean_object* v_n_1897_; lean_object* v___x_1898_; lean_object* v_toCheck_1900_; lean_object* v___y_1901_; lean_object* v___x_1905_; lean_object* v___x_1906_; uint8_t v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; uint8_t v___x_1911_; 
v_ngen_1881_ = lean_ctor_get(v_a_1877_, 3);
lean_inc_ref(v_ngen_1881_);
v_binderName_1882_ = lean_ctor_get(v_type_1873_, 0);
lean_inc(v_binderName_1882_);
v_binderType_1883_ = lean_ctor_get(v_type_1873_, 1);
lean_inc_ref_n(v_binderType_1883_, 2);
v_body_1884_ = lean_ctor_get(v_type_1873_, 2);
lean_inc_ref(v_body_1884_);
v_binderInfo_1885_ = lean_ctor_get_uint8(v_type_1873_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_1873_);
v_env_1886_ = lean_ctor_get(v_a_1877_, 0);
lean_inc_ref_n(v_env_1886_, 2);
v_lctx_1887_ = lean_ctor_get(v_a_1877_, 1);
lean_inc_ref(v_lctx_1887_);
v_lparams_1888_ = lean_ctor_get(v_a_1877_, 2);
lean_inc_n(v_lparams_1888_, 2);
v_safety_1889_ = lean_ctor_get_uint8(v_a_1877_, sizeof(void*)*4);
v_allowPrimitive_1890_ = lean_ctor_get_uint8(v_a_1877_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_1877_);
v_namePrefix_1891_ = lean_ctor_get(v_ngen_1881_, 0);
lean_inc_n(v_namePrefix_1891_, 2);
v_idx_1892_ = lean_ctor_get(v_ngen_1881_, 1);
lean_inc_n(v_idx_1892_, 2);
lean_dec_ref(v_ngen_1881_);
v_params_1893_ = lean_ctor_get(v_stats_1872_, 5);
v___x_1894_ = l_Lean_Name_num___override(v_namePrefix_1891_, v_idx_1892_);
lean_inc(v___x_1894_);
v___x_1895_ = l_Lean_Expr_fvar___override(v___x_1894_);
v_one_1896_ = lean_unsigned_to_nat(1u);
v_n_1897_ = lean_nat_sub(v_x_1876_, v_one_1896_);
lean_dec(v_x_1876_);
v___x_1898_ = lean_expr_consume_type_annotations(v_binderType_1883_);
v___x_1905_ = lean_nat_add(v_idx_1892_, v_one_1896_);
lean_dec(v_idx_1892_);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v_namePrefix_1891_);
lean_ctor_set(v___x_1906_, 1, v___x_1905_);
v___x_1907_ = 0;
v___x_1908_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_1887_, v___x_1894_, v_binderName_1882_, v___x_1898_, v_binderInfo_1885_, v___x_1907_);
lean_inc_ref(v___x_1908_);
v___x_1909_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_1909_, 0, v_env_1886_);
lean_ctor_set(v___x_1909_, 1, v___x_1908_);
lean_ctor_set(v___x_1909_, 2, v_lparams_1888_);
lean_ctor_set(v___x_1909_, 3, v___x_1906_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*4, v_safety_1889_);
lean_ctor_set_uint8(v___x_1909_, sizeof(void*)*4 + 1, v_allowPrimitive_1890_);
v___x_1910_ = lean_array_get_size(v_params_1893_);
v___x_1911_ = lean_nat_dec_le(v___x_1910_, v_i_1874_);
if (v___x_1911_ == 0)
{
lean_dec_ref(v___x_1908_);
lean_dec(v_lparams_1888_);
lean_dec_ref(v_env_1886_);
lean_dec_ref(v_binderType_1883_);
v_toCheck_1900_ = v_toCheck_1875_;
v___y_1901_ = v___x_1909_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_ensureType___boxed), 3, 1);
lean_closure_set(v___x_1912_, 0, v_binderType_1883_);
v___x_1913_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_1886_, v_safety_1889_, v___x_1908_, v_lparams_1888_, v___x_1912_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1916_; uint8_t v_isShared_1917_; uint8_t v_isSharedCheck_1921_; 
lean_dec_ref(v___x_1909_);
lean_dec(v_n_1897_);
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_body_1884_);
lean_dec_ref(v_toCheck_1875_);
lean_dec(v_i_1874_);
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1916_ = v___x_1913_;
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
else
{
lean_inc(v_a_1914_);
lean_dec(v___x_1913_);
v___x_1916_ = lean_box(0);
v_isShared_1917_ = v_isSharedCheck_1921_;
goto v_resetjp_1915_;
}
v_resetjp_1915_:
{
lean_object* v___x_1919_; 
if (v_isShared_1917_ == 0)
{
v___x_1919_ = v___x_1916_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_a_1914_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1923_; uint8_t v___x_1924_; 
v_a_1922_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1922_);
lean_dec_ref(v___x_1913_);
v___x_1923_ = l_Lean_Expr_sortLevel_x21(v_a_1922_);
lean_dec(v_a_1922_);
v___x_1924_ = l_Lean_Level_isZero(v___x_1923_);
lean_dec(v___x_1923_);
if (v___x_1924_ == 0)
{
lean_object* v___x_1925_; 
lean_inc_ref(v___x_1895_);
v___x_1925_ = lean_array_push(v_toCheck_1875_, v___x_1895_);
v_toCheck_1900_ = v___x_1925_;
v___y_1901_ = v___x_1909_;
goto v___jp_1899_;
}
else
{
v_toCheck_1900_ = v_toCheck_1875_;
v___y_1901_ = v___x_1909_;
goto v___jp_1899_;
}
}
}
v___jp_1899_:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_expr_instantiate1(v_body_1884_, v___x_1895_);
lean_dec_ref(v___x_1895_);
lean_dec_ref(v_body_1884_);
v___x_1903_ = lean_nat_add(v_i_1874_, v_one_1896_);
lean_dec(v_i_1874_);
v_type_1873_ = v___x_1902_;
v_i_1874_ = v___x_1903_;
v_toCheck_1875_ = v_toCheck_1900_;
v_x_1876_ = v_n_1897_;
v_a_1877_ = v___y_1901_;
goto _start;
}
}
else
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
lean_dec_ref(v_a_1877_);
lean_dec(v_x_1876_);
lean_dec(v_i_1874_);
v___x_1926_ = lean_array_get_size(v_toCheck_1875_);
v___x_1927_ = lean_nat_dec_lt(v_zero_1878_, v___x_1926_);
if (v___x_1927_ == 0)
{
lean_object* v___x_1928_; 
lean_dec_ref(v_toCheck_1875_);
lean_dec_ref(v_type_1873_);
v___x_1928_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__1));
return v___x_1928_;
}
else
{
if (v___x_1927_ == 0)
{
lean_object* v___x_1929_; lean_object* v___x_1930_; 
lean_dec_ref(v_toCheck_1875_);
lean_dec_ref(v_type_1873_);
v___x_1929_ = lean_box(v___x_1927_);
v___x_1930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1929_);
return v___x_1930_;
}
else
{
lean_object* v_nargs_1931_; lean_object* v_dummy_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; size_t v___x_1937_; size_t v___x_1938_; uint8_t v___x_1939_; 
v_nargs_1931_ = l_Lean_Expr_getAppNumArgs(v_type_1873_);
v_dummy_1932_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
lean_inc(v_nargs_1931_);
v___x_1933_ = lean_mk_array(v_nargs_1931_, v_dummy_1932_);
v___x_1934_ = lean_unsigned_to_nat(1u);
v___x_1935_ = lean_nat_sub(v_nargs_1931_, v___x_1934_);
lean_dec(v_nargs_1931_);
v___x_1936_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_1873_, v___x_1933_, v___x_1935_);
v___x_1937_ = ((size_t)0ULL);
v___x_1938_ = lean_usize_of_nat(v___x_1926_);
v___x_1939_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_AddInductive_isLargeEliminator_loop_spec__1(v___x_1936_, v_toCheck_1875_, v___x_1937_, v___x_1938_);
lean_dec_ref(v_toCheck_1875_);
lean_dec_ref(v___x_1936_);
if (v___x_1939_ == 0)
{
lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1940_ = lean_box(v___x_1927_);
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
return v___x_1941_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; 
v___x_1942_ = lean_box(v_isZero_1879_);
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
return v___x_1943_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator_loop___boxed(lean_object* v_stats_1944_, lean_object* v_type_1945_, lean_object* v_i_1946_, lean_object* v_toCheck_1947_, lean_object* v_x_1948_, lean_object* v_a_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean4Lean_AddInductive_isLargeEliminator_loop(v_stats_1944_, v_type_1945_, v_i_1946_, v_toCheck_1947_, v_x_1948_, v_a_1949_);
lean_dec_ref(v_stats_1944_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator(lean_object* v_stats_1953_, lean_object* v_indTypes_1954_, lean_object* v_a_1955_){
_start:
{
uint8_t v_isNotZero_1956_; 
v_isNotZero_1956_ = lean_ctor_get_uint8(v_stats_1953_, sizeof(void*)*6);
if (v_isNotZero_1956_ == 0)
{
lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1957_ = lean_array_get_size(v_indTypes_1954_);
v___x_1958_ = lean_unsigned_to_nat(1u);
v___x_1959_ = lean_nat_dec_eq(v___x_1957_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_object* v___x_1960_; lean_object* v___x_1961_; 
v___x_1960_ = lean_box(v_isNotZero_1956_);
v___x_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
return v___x_1961_;
}
else
{
lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_ctors_1964_; 
v___x_1962_ = lean_unsigned_to_nat(0u);
v___x_1963_ = lean_array_fget_borrowed(v_indTypes_1954_, v___x_1962_);
v_ctors_1964_ = lean_ctor_get(v___x_1963_, 2);
if (lean_obj_tag(v_ctors_1964_) == 0)
{
lean_object* v___x_1965_; 
v___x_1965_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__1));
return v___x_1965_;
}
else
{
lean_object* v_tail_1966_; 
v_tail_1966_ = lean_ctor_get(v_ctors_1964_, 1);
if (lean_obj_tag(v_tail_1966_) == 0)
{
lean_object* v_head_1967_; lean_object* v_type_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_head_1967_ = lean_ctor_get(v_ctors_1964_, 0);
v_type_1968_ = lean_ctor_get(v_head_1967_, 1);
v___x_1969_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
v___x_1970_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v_a_1955_);
lean_inc_ref(v_type_1968_);
v___x_1971_ = l_Lean4Lean_AddInductive_isLargeEliminator_loop(v_stats_1953_, v_type_1968_, v___x_1962_, v___x_1969_, v___x_1970_, v_a_1955_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1972_ = lean_box(v_isNotZero_1956_);
v___x_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
}
}
}
else
{
lean_object* v___x_1974_; 
v___x_1974_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator_loop___closed__1));
return v___x_1974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isLargeEliminator___boxed(lean_object* v_stats_1975_, lean_object* v_indTypes_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v_res_1978_; 
v_res_1978_ = l_Lean4Lean_AddInductive_isLargeEliminator(v_stats_1975_, v_indTypes_1976_, v_a_1977_);
lean_dec_ref(v_a_1977_);
lean_dec_ref(v_indTypes_1976_);
lean_dec_ref(v_stats_1975_);
return v_res_1978_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00Lean4Lean_AddInductive_getElimLevel_loop_spec__0(lean_object* v_a_1979_, lean_object* v_x_1980_){
_start:
{
if (lean_obj_tag(v_x_1980_) == 0)
{
uint8_t v___x_1981_; 
v___x_1981_ = 0;
return v___x_1981_;
}
else
{
lean_object* v_head_1982_; lean_object* v_tail_1983_; uint8_t v___x_1984_; 
v_head_1982_ = lean_ctor_get(v_x_1980_, 0);
v_tail_1983_ = lean_ctor_get(v_x_1980_, 1);
v___x_1984_ = lean_name_eq(v_a_1979_, v_head_1982_);
if (v___x_1984_ == 0)
{
v_x_1980_ = v_tail_1983_;
goto _start;
}
else
{
return v___x_1984_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00Lean4Lean_AddInductive_getElimLevel_loop_spec__0___boxed(lean_object* v_a_1986_, lean_object* v_x_1987_){
_start:
{
uint8_t v_res_1988_; lean_object* v_r_1989_; 
v_res_1988_ = l_List_elem___at___00Lean4Lean_AddInductive_getElimLevel_loop_spec__0(v_a_1986_, v_x_1987_);
lean_dec(v_x_1987_);
lean_dec(v_a_1986_);
v_r_1989_ = lean_box(v_res_1988_);
return v_r_1989_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel_loop(lean_object* v_lparams_1993_, lean_object* v_u_1994_, lean_object* v_i_1995_){
_start:
{
uint8_t v___x_1996_; 
v___x_1996_ = l_List_elem___at___00Lean4Lean_AddInductive_getElimLevel_loop_spec__0(v_u_1994_, v_lparams_1993_);
if (v___x_1996_ == 0)
{
lean_object* v___x_1997_; 
lean_dec(v_i_1995_);
v___x_1997_ = l_Lean_Level_param___override(v_u_1994_);
return v___x_1997_;
}
else
{
lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
lean_dec(v_u_1994_);
v___x_1998_ = ((lean_object*)(l_Lean4Lean_AddInductive_getElimLevel_loop___closed__1));
lean_inc(v_i_1995_);
v___x_1999_ = lean_name_append_index_after(v___x_1998_, v_i_1995_);
v___x_2000_ = lean_unsigned_to_nat(1u);
v___x_2001_ = lean_nat_add(v_i_1995_, v___x_2000_);
lean_dec(v_i_1995_);
v_u_1994_ = v___x_1999_;
v_i_1995_ = v___x_2001_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel_loop___boxed(lean_object* v_lparams_2003_, lean_object* v_u_2004_, lean_object* v_i_2005_){
_start:
{
lean_object* v_res_2006_; 
v_res_2006_ = l_Lean4Lean_AddInductive_getElimLevel_loop(v_lparams_2003_, v_u_2004_, v_i_2005_);
lean_dec(v_lparams_2003_);
return v_res_2006_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel(lean_object* v_stats_2009_, lean_object* v_indTypes_2010_, lean_object* v_a_2011_){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = l_Lean4Lean_AddInductive_isLargeEliminator(v_stats_2009_, v_indTypes_2010_, v_a_2011_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2020_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2020_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2020_ == 0)
{
v___x_2015_ = v___x_2012_;
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_a_2013_);
lean_dec(v___x_2012_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2020_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v___x_2018_; 
if (v_isShared_2016_ == 0)
{
v___x_2018_ = v___x_2015_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2019_; 
v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
v___x_2018_ = v_reuseFailAlloc_2019_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
return v___x_2018_;
}
}
}
else
{
lean_object* v_a_2021_; lean_object* v___x_2023_; uint8_t v_isShared_2024_; uint8_t v_isSharedCheck_2034_; 
v_a_2021_ = lean_ctor_get(v___x_2012_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2012_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2023_ = v___x_2012_;
v_isShared_2024_ = v_isSharedCheck_2034_;
goto v_resetjp_2022_;
}
else
{
lean_inc(v_a_2021_);
lean_dec(v___x_2012_);
v___x_2023_ = lean_box(0);
v_isShared_2024_ = v_isSharedCheck_2034_;
goto v_resetjp_2022_;
}
v_resetjp_2022_:
{
uint8_t v___x_2025_; 
v___x_2025_ = lean_unbox(v_a_2021_);
lean_dec(v_a_2021_);
if (v___x_2025_ == 0)
{
lean_object* v___x_2026_; 
lean_del_object(v___x_2023_);
v___x_2026_ = ((lean_object*)(l_Lean4Lean_AddInductive_getElimLevel___closed__0));
return v___x_2026_;
}
else
{
lean_object* v_lparams_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2032_; 
v_lparams_2027_ = lean_ctor_get(v_a_2011_, 2);
v___x_2028_ = ((lean_object*)(l_Lean4Lean_AddInductive_getElimLevel_loop___closed__1));
v___x_2029_ = lean_unsigned_to_nat(1u);
v___x_2030_ = l_Lean4Lean_AddInductive_getElimLevel_loop(v_lparams_2027_, v___x_2028_, v___x_2029_);
if (v_isShared_2024_ == 0)
{
lean_ctor_set(v___x_2023_, 0, v___x_2030_);
v___x_2032_ = v___x_2023_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getElimLevel___boxed(lean_object* v_stats_2035_, lean_object* v_indTypes_2036_, lean_object* v_a_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean4Lean_AddInductive_getElimLevel(v_stats_2035_, v_indTypes_2036_, v_a_2037_);
lean_dec_ref(v_a_2037_);
lean_dec_ref(v_indTypes_2036_);
lean_dec_ref(v_stats_2035_);
return v_res_2038_;
}
}
LEAN_EXPORT uint8_t l_Lean4Lean_AddInductive_isKTarget_loop(lean_object* v_stats_2039_, lean_object* v_i_2040_, lean_object* v_x_2041_){
_start:
{
if (lean_obj_tag(v_x_2041_) == 7)
{
lean_object* v_body_2042_; lean_object* v_params_2043_; lean_object* v___x_2044_; uint8_t v___x_2045_; 
v_body_2042_ = lean_ctor_get(v_x_2041_, 2);
v_params_2043_ = lean_ctor_get(v_stats_2039_, 5);
v___x_2044_ = lean_array_get_size(v_params_2043_);
v___x_2045_ = lean_nat_dec_lt(v_i_2040_, v___x_2044_);
if (v___x_2045_ == 0)
{
lean_dec(v_i_2040_);
return v___x_2045_;
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = lean_unsigned_to_nat(1u);
v___x_2047_ = lean_nat_add(v_i_2040_, v___x_2046_);
lean_dec(v_i_2040_);
v_i_2040_ = v___x_2047_;
v_x_2041_ = v_body_2042_;
goto _start;
}
}
else
{
uint8_t v___x_2049_; 
lean_dec(v_i_2040_);
v___x_2049_ = 1;
return v___x_2049_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget_loop___boxed(lean_object* v_stats_2050_, lean_object* v_i_2051_, lean_object* v_x_2052_){
_start:
{
uint8_t v_res_2053_; lean_object* v_r_2054_; 
v_res_2053_ = l_Lean4Lean_AddInductive_isKTarget_loop(v_stats_2050_, v_i_2051_, v_x_2052_);
lean_dec_ref(v_x_2052_);
lean_dec_ref(v_stats_2050_);
v_r_2054_ = lean_box(v_res_2053_);
return v_r_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget___redArg(lean_object* v_stats_2058_, lean_object* v_indTypes_2059_){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; uint8_t v___x_2064_; 
v___x_2062_ = lean_array_get_size(v_indTypes_2059_);
v___x_2063_ = lean_unsigned_to_nat(1u);
v___x_2064_ = lean_nat_dec_eq(v___x_2062_, v___x_2063_);
if (v___x_2064_ == 0)
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_box(v___x_2064_);
v___x_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
else
{
lean_object* v_resultLevel_2067_; uint8_t v___x_2068_; 
v_resultLevel_2067_ = lean_ctor_get(v_stats_2058_, 2);
v___x_2068_ = l_Lean_Level_isZero(v_resultLevel_2067_);
if (v___x_2068_ == 0)
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = lean_box(v___x_2068_);
v___x_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2070_, 0, v___x_2069_);
return v___x_2070_;
}
else
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_ctors_2073_; 
v___x_2071_ = lean_unsigned_to_nat(0u);
v___x_2072_ = lean_array_fget_borrowed(v_indTypes_2059_, v___x_2071_);
v_ctors_2073_ = lean_ctor_get(v___x_2072_, 2);
if (lean_obj_tag(v_ctors_2073_) == 1)
{
lean_object* v_tail_2074_; 
v_tail_2074_ = lean_ctor_get(v_ctors_2073_, 1);
if (lean_obj_tag(v_tail_2074_) == 0)
{
lean_object* v_head_2075_; lean_object* v_type_2076_; uint8_t v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_head_2075_ = lean_ctor_get(v_ctors_2073_, 0);
v_type_2076_ = lean_ctor_get(v_head_2075_, 1);
v___x_2077_ = l_Lean4Lean_AddInductive_isKTarget_loop(v_stats_2058_, v___x_2071_, v_type_2076_);
v___x_2078_ = lean_box(v___x_2077_);
v___x_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2079_, 0, v___x_2078_);
return v___x_2079_;
}
else
{
goto v___jp_2060_;
}
}
else
{
goto v___jp_2060_;
}
}
}
v___jp_2060_:
{
lean_object* v___x_2061_; 
v___x_2061_ = ((lean_object*)(l_Lean4Lean_AddInductive_isKTarget___redArg___closed__0));
return v___x_2061_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget___redArg___boxed(lean_object* v_stats_2080_, lean_object* v_indTypes_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean4Lean_AddInductive_isKTarget___redArg(v_stats_2080_, v_indTypes_2081_);
lean_dec_ref(v_indTypes_2081_);
lean_dec_ref(v_stats_2080_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget(lean_object* v_stats_2083_, lean_object* v_indTypes_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2086_; 
v___x_2086_ = l_Lean4Lean_AddInductive_isKTarget___redArg(v_stats_2083_, v_indTypes_2084_);
return v___x_2086_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_isKTarget___boxed(lean_object* v_stats_2087_, lean_object* v_indTypes_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l_Lean4Lean_AddInductive_isKTarget(v_stats_2087_, v_indTypes_2088_, v_a_2089_);
lean_dec_ref(v_a_2089_);
lean_dec_ref(v_indTypes_2088_);
lean_dec_ref(v_stats_2087_);
return v_res_2090_;
}
}
static lean_object* _init_l_Lean4Lean_AddInductive_getIIndices___closed__3(void){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; 
v___x_2094_ = ((lean_object*)(l_Lean4Lean_AddInductive_getIIndices___closed__2));
v___x_2095_ = lean_unsigned_to_nat(14u);
v___x_2096_ = lean_unsigned_to_nat(22u);
v___x_2097_ = ((lean_object*)(l_Lean4Lean_AddInductive_getIIndices___closed__1));
v___x_2098_ = ((lean_object*)(l_Lean4Lean_AddInductive_getIIndices___closed__0));
v___x_2099_ = l_mkPanicMessageWithDecl(v___x_2098_, v___x_2097_, v___x_2096_, v___x_2095_, v___x_2094_);
return v___x_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getIIndices(lean_object* v_stats_2100_, lean_object* v_t_2101_){
_start:
{
lean_object* v___y_2103_; lean_object* v___x_2116_; 
lean_inc_ref(v_t_2101_);
lean_inc_ref(v_stats_2100_);
v___x_2116_ = l_Lean4Lean_AddInductive_isValidIndApp_x3f(v_stats_2100_, v_t_2101_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_unsigned_to_nat(0u);
v___x_2118_ = lean_obj_once(&l_Lean4Lean_AddInductive_getIIndices___closed__3, &l_Lean4Lean_AddInductive_getIIndices___closed__3_once, _init_l_Lean4Lean_AddInductive_getIIndices___closed__3);
v___x_2119_ = l_panic___redArg(v___x_2117_, v___x_2118_);
v___y_2103_ = v___x_2119_;
goto v___jp_2102_;
}
else
{
lean_object* v_val_2120_; 
v_val_2120_ = lean_ctor_get(v___x_2116_, 0);
lean_inc(v_val_2120_);
lean_dec_ref(v___x_2116_);
v___y_2103_ = v_val_2120_;
goto v___jp_2102_;
}
v___jp_2102_:
{
lean_object* v_params_2104_; lean_object* v_nargs_2105_; lean_object* v_dummy_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; 
v_params_2104_ = lean_ctor_get(v_stats_2100_, 5);
lean_inc_ref(v_params_2104_);
lean_dec_ref(v_stats_2100_);
v_nargs_2105_ = l_Lean_Expr_getAppNumArgs(v_t_2101_);
v_dummy_2106_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
lean_inc(v_nargs_2105_);
v___x_2107_ = lean_mk_array(v_nargs_2105_, v_dummy_2106_);
v___x_2108_ = lean_unsigned_to_nat(1u);
v___x_2109_ = lean_nat_sub(v_nargs_2105_, v___x_2108_);
lean_dec(v_nargs_2105_);
v_a_2110_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_2101_, v___x_2107_, v___x_2109_);
v___x_2111_ = lean_array_get_size(v_params_2104_);
lean_dec_ref(v_params_2104_);
v___x_2112_ = lean_array_get_size(v_a_2110_);
v___x_2113_ = l_Array_toSubarray___redArg(v_a_2110_, v___x_2111_, v___x_2112_);
v___x_2114_ = l_Subarray_copy___redArg(v___x_2113_);
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___y_2103_);
lean_ctor_set(v___x_2115_, 1, v___x_2114_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___redArg(lean_object* v_stats_2121_, lean_object* v_type_2122_, lean_object* v_i_2123_, lean_object* v_indices_2124_, lean_object* v_fuel_2125_, lean_object* v_k_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v_zero_2128_; uint8_t v_isZero_2129_; 
v_zero_2128_ = lean_unsigned_to_nat(0u);
v_isZero_2129_ = lean_nat_dec_eq(v_fuel_2125_, v_zero_2128_);
if (v_isZero_2129_ == 1)
{
lean_object* v___x_2130_; 
lean_dec_ref(v_a_2127_);
lean_dec_ref(v_k_2126_);
lean_dec(v_fuel_2125_);
lean_dec_ref(v_indices_2124_);
lean_dec(v_i_2123_);
lean_dec_ref(v_type_2122_);
v___x_2130_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__0));
return v___x_2130_;
}
else
{
if (lean_obj_tag(v_type_2122_) == 7)
{
lean_object* v_binderName_2131_; lean_object* v_binderType_2132_; lean_object* v_body_2133_; uint8_t v_binderInfo_2134_; lean_object* v_params_2135_; lean_object* v_one_2136_; lean_object* v_n_2137_; lean_object* v___x_2138_; uint8_t v___x_2139_; 
v_binderName_2131_ = lean_ctor_get(v_type_2122_, 0);
lean_inc(v_binderName_2131_);
v_binderType_2132_ = lean_ctor_get(v_type_2122_, 1);
lean_inc_ref(v_binderType_2132_);
v_body_2133_ = lean_ctor_get(v_type_2122_, 2);
lean_inc_ref(v_body_2133_);
v_binderInfo_2134_ = lean_ctor_get_uint8(v_type_2122_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_2122_);
v_params_2135_ = lean_ctor_get(v_stats_2121_, 5);
v_one_2136_ = lean_unsigned_to_nat(1u);
v_n_2137_ = lean_nat_sub(v_fuel_2125_, v_one_2136_);
lean_dec(v_fuel_2125_);
v___x_2138_ = lean_array_get_size(v_params_2135_);
v___x_2139_ = lean_nat_dec_lt(v_i_2123_, v___x_2138_);
if (v___x_2139_ == 0)
{
lean_object* v_ngen_2140_; lean_object* v_env_2141_; lean_object* v_lctx_2142_; lean_object* v_lparams_2143_; uint8_t v_safety_2144_; uint8_t v_allowPrimitive_2145_; lean_object* v_namePrefix_2146_; lean_object* v_idx_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; uint8_t v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; 
v_ngen_2140_ = lean_ctor_get(v_a_2127_, 3);
lean_inc_ref(v_ngen_2140_);
v_env_2141_ = lean_ctor_get(v_a_2127_, 0);
lean_inc_ref_n(v_env_2141_, 2);
v_lctx_2142_ = lean_ctor_get(v_a_2127_, 1);
lean_inc_ref(v_lctx_2142_);
v_lparams_2143_ = lean_ctor_get(v_a_2127_, 2);
lean_inc_n(v_lparams_2143_, 2);
v_safety_2144_ = lean_ctor_get_uint8(v_a_2127_, sizeof(void*)*4);
v_allowPrimitive_2145_ = lean_ctor_get_uint8(v_a_2127_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_2127_);
v_namePrefix_2146_ = lean_ctor_get(v_ngen_2140_, 0);
lean_inc_n(v_namePrefix_2146_, 2);
v_idx_2147_ = lean_ctor_get(v_ngen_2140_, 1);
lean_inc_n(v_idx_2147_, 2);
lean_dec_ref(v_ngen_2140_);
v___x_2148_ = lean_expr_consume_type_annotations(v_binderType_2132_);
v___x_2149_ = l_Lean_Name_num___override(v_namePrefix_2146_, v_idx_2147_);
v___x_2150_ = lean_nat_add(v_idx_2147_, v_one_2136_);
lean_dec(v_idx_2147_);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v_namePrefix_2146_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
lean_inc(v___x_2149_);
v___x_2152_ = l_Lean_Expr_fvar___override(v___x_2149_);
v___x_2153_ = 0;
v___x_2154_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2142_, v___x_2149_, v_binderName_2131_, v___x_2148_, v_binderInfo_2134_, v___x_2153_);
lean_inc_ref(v___x_2154_);
v___x_2155_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2155_, 0, v_env_2141_);
lean_ctor_set(v___x_2155_, 1, v___x_2154_);
lean_ctor_set(v___x_2155_, 2, v_lparams_2143_);
lean_ctor_set(v___x_2155_, 3, v___x_2151_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*4, v_safety_2144_);
lean_ctor_set_uint8(v___x_2155_, sizeof(void*)*4 + 1, v_allowPrimitive_2145_);
v___x_2156_ = lean_expr_instantiate1(v_body_2133_, v___x_2152_);
lean_dec_ref(v_body_2133_);
v___x_2157_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_2157_, 0, v___x_2156_);
v___x_2158_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_2141_, v_safety_2144_, v___x_2154_, v_lparams_2143_, v___x_2157_);
if (lean_obj_tag(v___x_2158_) == 0)
{
lean_object* v_a_2159_; lean_object* v___x_2161_; uint8_t v_isShared_2162_; uint8_t v_isSharedCheck_2166_; 
lean_dec_ref(v___x_2155_);
lean_dec_ref(v___x_2152_);
lean_dec(v_n_2137_);
lean_dec_ref(v_k_2126_);
lean_dec_ref(v_indices_2124_);
lean_dec(v_i_2123_);
v_a_2159_ = lean_ctor_get(v___x_2158_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2161_ = v___x_2158_;
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
else
{
lean_inc(v_a_2159_);
lean_dec(v___x_2158_);
v___x_2161_ = lean_box(0);
v_isShared_2162_ = v_isSharedCheck_2166_;
goto v_resetjp_2160_;
}
v_resetjp_2160_:
{
lean_object* v___x_2164_; 
if (v_isShared_2162_ == 0)
{
v___x_2164_ = v___x_2161_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v_a_2159_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2168_; 
v_a_2167_ = lean_ctor_get(v___x_2158_, 0);
lean_inc(v_a_2167_);
lean_dec_ref(v___x_2158_);
v___x_2168_ = lean_array_push(v_indices_2124_, v___x_2152_);
v_type_2122_ = v_a_2167_;
v_indices_2124_ = v___x_2168_;
v_fuel_2125_ = v_n_2137_;
v_a_2127_ = v___x_2155_;
goto _start;
}
}
else
{
lean_object* v_env_2170_; lean_object* v_lctx_2171_; lean_object* v_lparams_2172_; uint8_t v_safety_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
lean_dec_ref(v_binderType_2132_);
lean_dec(v_binderName_2131_);
v_env_2170_ = lean_ctor_get(v_a_2127_, 0);
v_lctx_2171_ = lean_ctor_get(v_a_2127_, 1);
v_lparams_2172_ = lean_ctor_get(v_a_2127_, 2);
v_safety_2173_ = lean_ctor_get_uint8(v_a_2127_, sizeof(void*)*4);
v___x_2174_ = l_Lean_instInhabitedExpr;
v___x_2175_ = lean_array_get_borrowed(v___x_2174_, v_params_2135_, v_i_2123_);
v___x_2176_ = lean_expr_instantiate1(v_body_2133_, v___x_2175_);
lean_dec_ref(v_body_2133_);
v___x_2177_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_2177_, 0, v___x_2176_);
lean_inc(v_lparams_2172_);
lean_inc_ref(v_lctx_2171_);
lean_inc_ref(v_env_2170_);
v___x_2178_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_2170_, v_safety_2173_, v_lctx_2171_, v_lparams_2172_, v___x_2177_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; lean_object* v___x_2181_; uint8_t v_isShared_2182_; uint8_t v_isSharedCheck_2186_; 
lean_dec(v_n_2137_);
lean_dec_ref(v_a_2127_);
lean_dec_ref(v_k_2126_);
lean_dec_ref(v_indices_2124_);
lean_dec(v_i_2123_);
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2181_ = v___x_2178_;
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
else
{
lean_inc(v_a_2179_);
lean_dec(v___x_2178_);
v___x_2181_ = lean_box(0);
v_isShared_2182_ = v_isSharedCheck_2186_;
goto v_resetjp_2180_;
}
v_resetjp_2180_:
{
lean_object* v___x_2184_; 
if (v_isShared_2182_ == 0)
{
v___x_2184_ = v___x_2181_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v_a_2179_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
}
else
{
lean_object* v_a_2187_; lean_object* v___x_2188_; 
v_a_2187_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2187_);
lean_dec_ref(v___x_2178_);
v___x_2188_ = lean_nat_add(v_i_2123_, v_one_2136_);
lean_dec(v_i_2123_);
v_type_2122_ = v_a_2187_;
v_i_2123_ = v___x_2188_;
v_fuel_2125_ = v_n_2137_;
goto _start;
}
}
}
else
{
lean_object* v___x_2190_; 
lean_dec(v_fuel_2125_);
lean_dec(v_i_2123_);
lean_dec_ref(v_type_2122_);
v___x_2190_ = lean_apply_2(v_k_2126_, v_indices_2124_, v_a_2127_);
return v___x_2190_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___redArg___boxed(lean_object* v_stats_2191_, lean_object* v_type_2192_, lean_object* v_i_2193_, lean_object* v_indices_2194_, lean_object* v_fuel_2195_, lean_object* v_k_2196_, lean_object* v_a_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___redArg(v_stats_2191_, v_type_2192_, v_i_2193_, v_indices_2194_, v_fuel_2195_, v_k_2196_, v_a_2197_);
lean_dec_ref(v_stats_2191_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1(lean_object* v_00_u03b1_2199_, lean_object* v_stats_2200_, lean_object* v_type_2201_, lean_object* v_i_2202_, lean_object* v_indices_2203_, lean_object* v_fuel_2204_, lean_object* v_k_2205_, lean_object* v_a_2206_){
_start:
{
lean_object* v___x_2207_; 
lean_inc_ref(v_a_2206_);
v___x_2207_ = l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___redArg(v_stats_2200_, v_type_2201_, v_i_2202_, v_indices_2203_, v_fuel_2204_, v_k_2205_, v_a_2206_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___boxed(lean_object* v_00_u03b1_2208_, lean_object* v_stats_2209_, lean_object* v_type_2210_, lean_object* v_i_2211_, lean_object* v_indices_2212_, lean_object* v_fuel_2213_, lean_object* v_k_2214_, lean_object* v_a_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1(v_00_u03b1_2208_, v_stats_2209_, v_type_2210_, v_i_2211_, v_indices_2212_, v_fuel_2213_, v_k_2214_, v_a_2215_);
lean_dec_ref(v_a_2215_);
lean_dec_ref(v_stats_2209_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0(lean_object* v_stats_2223_, lean_object* v_dIdx_2224_, lean_object* v_elimLevel_2225_, uint8_t v___x_2226_, lean_object* v___x_2227_, lean_object* v_recInfos_2228_, lean_object* v_indTypes_2229_, lean_object* v_k_2230_, lean_object* v___x_2231_, lean_object* v_indices_2232_, lean_object* v___y_2233_){
_start:
{
lean_object* v_ngen_2234_; lean_object* v_indConsts_2235_; lean_object* v_params_2236_; lean_object* v_env_2237_; lean_object* v_lctx_2238_; lean_object* v_lparams_2239_; uint8_t v_safety_2240_; uint8_t v_allowPrimitive_2241_; lean_object* v_namePrefix_2242_; lean_object* v_idx_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; uint8_t v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; uint8_t v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; uint8_t v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___y_2264_; uint8_t v___x_2276_; 
v_ngen_2234_ = lean_ctor_get(v___y_2233_, 3);
v_indConsts_2235_ = lean_ctor_get(v_stats_2223_, 4);
v_params_2236_ = lean_ctor_get(v_stats_2223_, 5);
v_env_2237_ = lean_ctor_get(v___y_2233_, 0);
v_lctx_2238_ = lean_ctor_get(v___y_2233_, 1);
v_lparams_2239_ = lean_ctor_get(v___y_2233_, 2);
v_safety_2240_ = lean_ctor_get_uint8(v___y_2233_, sizeof(void*)*4);
v_allowPrimitive_2241_ = lean_ctor_get_uint8(v___y_2233_, sizeof(void*)*4 + 1);
v_namePrefix_2242_ = lean_ctor_get(v_ngen_2234_, 0);
v_idx_2243_ = lean_ctor_get(v_ngen_2234_, 1);
v___x_2244_ = l_Lean_instInhabitedExpr;
v___x_2245_ = lean_array_get_borrowed(v___x_2244_, v_indConsts_2235_, v_dIdx_2224_);
lean_inc(v___x_2245_);
v___x_2246_ = l_Lean_mkAppN(v___x_2245_, v_params_2236_);
v___x_2247_ = l_Lean_mkAppN(v___x_2246_, v_indices_2232_);
v___x_2248_ = ((lean_object*)(l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__1));
v___x_2249_ = 0;
v___x_2250_ = lean_expr_consume_type_annotations(v___x_2247_);
lean_inc(v_idx_2243_);
lean_inc(v_namePrefix_2242_);
v___x_2251_ = l_Lean_Name_num___override(v_namePrefix_2242_, v_idx_2243_);
v___x_2252_ = lean_unsigned_to_nat(1u);
v___x_2253_ = lean_nat_add(v_idx_2243_, v___x_2252_);
lean_inc(v___x_2251_);
v___x_2254_ = l_Lean_Expr_fvar___override(v___x_2251_);
v___x_2255_ = 0;
lean_inc_ref(v_lctx_2238_);
v___x_2256_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2238_, v___x_2251_, v___x_2248_, v___x_2250_, v___x_2249_, v___x_2255_);
v___x_2257_ = lean_mk_empty_array_with_capacity(v___x_2252_);
lean_inc_ref(v___x_2254_);
v___x_2258_ = lean_array_push(v___x_2257_, v___x_2254_);
lean_inc(v_elimLevel_2225_);
v___x_2259_ = l_Lean_Expr_sort___override(v_elimLevel_2225_);
v___x_2260_ = 0;
lean_inc_ref_n(v___x_2256_, 2);
v___x_2261_ = l_Lean_LocalContext_mkForall(v___x_2256_, v___x_2258_, v___x_2259_, v___x_2226_, v___x_2260_);
lean_dec_ref(v___x_2259_);
lean_dec_ref(v___x_2258_);
v___x_2262_ = l_Lean_LocalContext_mkForall(v___x_2256_, v_indices_2232_, v___x_2261_, v___x_2226_, v___x_2260_);
lean_dec_ref(v___x_2261_);
v___x_2276_ = lean_nat_dec_lt(v___x_2252_, v___x_2231_);
if (v___x_2276_ == 0)
{
lean_object* v___x_2277_; 
v___x_2277_ = ((lean_object*)(l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__3));
v___y_2264_ = v___x_2277_;
goto v___jp_2263_;
}
else
{
lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; 
v___x_2278_ = ((lean_object*)(l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___closed__3));
v___x_2279_ = lean_nat_add(v_dIdx_2224_, v___x_2252_);
v___x_2280_ = lean_name_append_index_after(v___x_2278_, v___x_2279_);
v___y_2264_ = v___x_2280_;
goto v___jp_2263_;
}
v___jp_2263_:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; 
v___x_2265_ = lean_expr_consume_type_annotations(v___x_2262_);
lean_inc(v___x_2253_);
lean_inc_n(v_namePrefix_2242_, 2);
v___x_2266_ = l_Lean_Name_num___override(v_namePrefix_2242_, v___x_2253_);
v___x_2267_ = lean_nat_add(v___x_2253_, v___x_2252_);
lean_dec(v___x_2253_);
v___x_2268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2268_, 0, v_namePrefix_2242_);
lean_ctor_set(v___x_2268_, 1, v___x_2267_);
lean_inc(v___x_2266_);
v___x_2269_ = l_Lean_Expr_fvar___override(v___x_2266_);
v___x_2270_ = l_Lean_LocalContext_mkLocalDecl(v___x_2256_, v___x_2266_, v___y_2264_, v___x_2265_, v___x_2249_, v___x_2255_);
lean_inc(v_lparams_2239_);
lean_inc_ref(v_env_2237_);
v___x_2271_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2271_, 0, v_env_2237_);
lean_ctor_set(v___x_2271_, 1, v___x_2270_);
lean_ctor_set(v___x_2271_, 2, v_lparams_2239_);
lean_ctor_set(v___x_2271_, 3, v___x_2268_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*4, v_safety_2240_);
lean_ctor_set_uint8(v___x_2271_, sizeof(void*)*4 + 1, v_allowPrimitive_2241_);
v___x_2272_ = lean_nat_add(v_dIdx_2224_, v___x_2252_);
v___x_2273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2269_);
lean_ctor_set(v___x_2273_, 1, v___x_2227_);
lean_ctor_set(v___x_2273_, 2, v_indices_2232_);
lean_ctor_set(v___x_2273_, 3, v___x_2254_);
v___x_2274_ = lean_array_push(v_recInfos_2228_, v___x_2273_);
v___x_2275_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg(v_stats_2223_, v_indTypes_2229_, v_elimLevel_2225_, v___x_2272_, v___x_2274_, v_k_2230_, v___x_2271_);
lean_dec_ref(v___x_2271_);
return v___x_2275_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___boxed(lean_object* v_stats_2281_, lean_object* v_dIdx_2282_, lean_object* v_elimLevel_2283_, lean_object* v___x_2284_, lean_object* v___x_2285_, lean_object* v_recInfos_2286_, lean_object* v_indTypes_2287_, lean_object* v_k_2288_, lean_object* v___x_2289_, lean_object* v_indices_2290_, lean_object* v___y_2291_){
_start:
{
uint8_t v___x_1151__boxed_2292_; lean_object* v_res_2293_; 
v___x_1151__boxed_2292_ = lean_unbox(v___x_2284_);
v_res_2293_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0(v_stats_2281_, v_dIdx_2282_, v_elimLevel_2283_, v___x_1151__boxed_2292_, v___x_2285_, v_recInfos_2286_, v_indTypes_2287_, v_k_2288_, v___x_2289_, v_indices_2290_, v___y_2291_);
lean_dec_ref(v___y_2291_);
lean_dec(v___x_2289_);
lean_dec(v_dIdx_2282_);
return v_res_2293_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg(lean_object* v_stats_2294_, lean_object* v_indTypes_2295_, lean_object* v_elimLevel_2296_, lean_object* v_dIdx_2297_, lean_object* v_recInfos_2298_, lean_object* v_k_2299_, lean_object* v_a_2300_){
_start:
{
lean_object* v___x_2301_; uint8_t v___x_2302_; 
v___x_2301_ = lean_array_get_size(v_indTypes_2295_);
v___x_2302_ = lean_nat_dec_lt(v_dIdx_2297_, v___x_2301_);
if (v___x_2302_ == 0)
{
lean_object* v___x_2303_; 
lean_dec(v_dIdx_2297_);
lean_dec(v_elimLevel_2296_);
lean_dec_ref(v_indTypes_2295_);
lean_dec_ref(v_stats_2294_);
lean_inc_ref(v_a_2300_);
v___x_2303_ = lean_apply_2(v_k_2299_, v_recInfos_2298_, v_a_2300_);
return v___x_2303_;
}
else
{
lean_object* v___x_2304_; lean_object* v_type_2305_; lean_object* v_env_2306_; lean_object* v_lctx_2307_; lean_object* v_lparams_2308_; uint8_t v_safety_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2304_ = lean_array_fget_borrowed(v_indTypes_2295_, v_dIdx_2297_);
v_type_2305_ = lean_ctor_get(v___x_2304_, 1);
v_env_2306_ = lean_ctor_get(v_a_2300_, 0);
v_lctx_2307_ = lean_ctor_get(v_a_2300_, 1);
v_lparams_2308_ = lean_ctor_get(v_a_2300_, 2);
v_safety_2309_ = lean_ctor_get_uint8(v_a_2300_, sizeof(void*)*4);
lean_inc_ref(v_type_2305_);
v___x_2310_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_2310_, 0, v_type_2305_);
lean_inc(v_lparams_2308_);
lean_inc_ref(v_lctx_2307_);
lean_inc_ref(v_env_2306_);
v___x_2311_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_2306_, v_safety_2309_, v_lctx_2307_, v_lparams_2308_, v___x_2310_);
if (lean_obj_tag(v___x_2311_) == 0)
{
lean_object* v_a_2312_; lean_object* v___x_2314_; uint8_t v_isShared_2315_; uint8_t v_isSharedCheck_2319_; 
lean_dec_ref(v_k_2299_);
lean_dec_ref(v_recInfos_2298_);
lean_dec(v_dIdx_2297_);
lean_dec(v_elimLevel_2296_);
lean_dec_ref(v_indTypes_2295_);
lean_dec_ref(v_stats_2294_);
v_a_2312_ = lean_ctor_get(v___x_2311_, 0);
v_isSharedCheck_2319_ = !lean_is_exclusive(v___x_2311_);
if (v_isSharedCheck_2319_ == 0)
{
v___x_2314_ = v___x_2311_;
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
else
{
lean_inc(v_a_2312_);
lean_dec(v___x_2311_);
v___x_2314_ = lean_box(0);
v_isShared_2315_ = v_isSharedCheck_2319_;
goto v_resetjp_2313_;
}
v_resetjp_2313_:
{
lean_object* v___x_2317_; 
if (v_isShared_2315_ == 0)
{
v___x_2317_ = v___x_2314_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_a_2312_);
v___x_2317_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
return v___x_2317_;
}
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___f_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v_a_2320_ = lean_ctor_get(v___x_2311_, 0);
lean_inc(v_a_2320_);
lean_dec_ref(v___x_2311_);
v___x_2321_ = lean_unsigned_to_nat(0u);
v___x_2322_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
v___x_2323_ = lean_box(v___x_2302_);
lean_inc_ref(v_stats_2294_);
v___f_2324_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___lam__0___boxed), 11, 9);
lean_closure_set(v___f_2324_, 0, v_stats_2294_);
lean_closure_set(v___f_2324_, 1, v_dIdx_2297_);
lean_closure_set(v___f_2324_, 2, v_elimLevel_2296_);
lean_closure_set(v___f_2324_, 3, v___x_2323_);
lean_closure_set(v___f_2324_, 4, v___x_2322_);
lean_closure_set(v___f_2324_, 5, v_recInfos_2298_);
lean_closure_set(v___f_2324_, 6, v_indTypes_2295_);
lean_closure_set(v___f_2324_, 7, v_k_2299_);
lean_closure_set(v___f_2324_, 8, v___x_2301_);
v___x_2325_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v_a_2300_);
v___x_2326_ = l_Lean4Lean_AddInductive_mkRecInfos_loopArgs1___redArg(v_stats_2294_, v_a_2320_, v___x_2321_, v___x_2322_, v___x_2325_, v___f_2324_, v_a_2300_);
lean_dec_ref(v_stats_2294_);
return v___x_2326_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg___boxed(lean_object* v_stats_2327_, lean_object* v_indTypes_2328_, lean_object* v_elimLevel_2329_, lean_object* v_dIdx_2330_, lean_object* v_recInfos_2331_, lean_object* v_k_2332_, lean_object* v_a_2333_){
_start:
{
lean_object* v_res_2334_; 
v_res_2334_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg(v_stats_2327_, v_indTypes_2328_, v_elimLevel_2329_, v_dIdx_2330_, v_recInfos_2331_, v_k_2332_, v_a_2333_);
lean_dec_ref(v_a_2333_);
return v_res_2334_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1(lean_object* v_stats_2335_, lean_object* v_indTypes_2336_, lean_object* v_elimLevel_2337_, lean_object* v_00_u03b1_2338_, lean_object* v_dIdx_2339_, lean_object* v_recInfos_2340_, lean_object* v_k_2341_, lean_object* v_a_2342_){
_start:
{
lean_object* v___x_2343_; 
v___x_2343_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg(v_stats_2335_, v_indTypes_2336_, v_elimLevel_2337_, v_dIdx_2339_, v_recInfos_2340_, v_k_2341_, v_a_2342_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___boxed(lean_object* v_stats_2344_, lean_object* v_indTypes_2345_, lean_object* v_elimLevel_2346_, lean_object* v_00_u03b1_2347_, lean_object* v_dIdx_2348_, lean_object* v_recInfos_2349_, lean_object* v_k_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd1(v_stats_2344_, v_indTypes_2345_, v_elimLevel_2346_, v_00_u03b1_2347_, v_dIdx_2348_, v_recInfos_2349_, v_k_2350_, v_a_2351_);
lean_dec_ref(v_a_2351_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop___redArg(lean_object* v_stats_2353_, lean_object* v_k_2354_, lean_object* v_t_2355_, lean_object* v_i_2356_, lean_object* v_bu_2357_, lean_object* v_u_2358_, lean_object* v_x_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v_zero_2361_; uint8_t v_isZero_2362_; 
v_zero_2361_ = lean_unsigned_to_nat(0u);
v_isZero_2362_ = lean_nat_dec_eq(v_x_2359_, v_zero_2361_);
if (v_isZero_2362_ == 1)
{
lean_object* v___x_2363_; 
lean_dec_ref(v_a_2360_);
lean_dec(v_x_2359_);
lean_dec_ref(v_u_2358_);
lean_dec_ref(v_bu_2357_);
lean_dec(v_i_2356_);
lean_dec_ref(v_t_2355_);
lean_dec_ref(v_k_2354_);
lean_dec_ref(v_stats_2353_);
v___x_2363_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__0));
return v___x_2363_;
}
else
{
if (lean_obj_tag(v_t_2355_) == 7)
{
lean_object* v_binderName_2364_; lean_object* v_binderType_2365_; lean_object* v_body_2366_; uint8_t v_binderInfo_2367_; lean_object* v_params_2368_; lean_object* v_one_2369_; lean_object* v_n_2370_; lean_object* v___x_2371_; uint8_t v___x_2372_; 
v_binderName_2364_ = lean_ctor_get(v_t_2355_, 0);
lean_inc(v_binderName_2364_);
v_binderType_2365_ = lean_ctor_get(v_t_2355_, 1);
lean_inc_ref(v_binderType_2365_);
v_body_2366_ = lean_ctor_get(v_t_2355_, 2);
lean_inc_ref(v_body_2366_);
v_binderInfo_2367_ = lean_ctor_get_uint8(v_t_2355_, sizeof(void*)*3 + 8);
lean_dec_ref(v_t_2355_);
v_params_2368_ = lean_ctor_get(v_stats_2353_, 5);
v_one_2369_ = lean_unsigned_to_nat(1u);
v_n_2370_ = lean_nat_sub(v_x_2359_, v_one_2369_);
lean_dec(v_x_2359_);
v___x_2371_ = lean_array_get_size(v_params_2368_);
v___x_2372_ = lean_nat_dec_lt(v_i_2356_, v___x_2371_);
if (v___x_2372_ == 0)
{
lean_object* v_ngen_2373_; lean_object* v_env_2374_; lean_object* v_lctx_2375_; lean_object* v_lparams_2376_; uint8_t v_safety_2377_; uint8_t v_allowPrimitive_2378_; lean_object* v_namePrefix_2379_; lean_object* v_idx_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; 
v_ngen_2373_ = lean_ctor_get(v_a_2360_, 3);
lean_inc_ref(v_ngen_2373_);
v_env_2374_ = lean_ctor_get(v_a_2360_, 0);
lean_inc_ref(v_env_2374_);
v_lctx_2375_ = lean_ctor_get(v_a_2360_, 1);
lean_inc_ref(v_lctx_2375_);
v_lparams_2376_ = lean_ctor_get(v_a_2360_, 2);
lean_inc(v_lparams_2376_);
v_safety_2377_ = lean_ctor_get_uint8(v_a_2360_, sizeof(void*)*4);
v_allowPrimitive_2378_ = lean_ctor_get_uint8(v_a_2360_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_2360_);
v_namePrefix_2379_ = lean_ctor_get(v_ngen_2373_, 0);
lean_inc_n(v_namePrefix_2379_, 2);
v_idx_2380_ = lean_ctor_get(v_ngen_2373_, 1);
lean_inc_n(v_idx_2380_, 2);
lean_dec_ref(v_ngen_2373_);
lean_inc_ref(v_binderType_2365_);
v___x_2381_ = lean_expr_consume_type_annotations(v_binderType_2365_);
v___x_2382_ = l_Lean_Name_num___override(v_namePrefix_2379_, v_idx_2380_);
v___x_2383_ = lean_nat_add(v_idx_2380_, v_one_2369_);
lean_dec(v_idx_2380_);
v___x_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2384_, 0, v_namePrefix_2379_);
lean_ctor_set(v___x_2384_, 1, v___x_2383_);
v___x_2385_ = 0;
lean_inc(v___x_2382_);
v___x_2386_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2375_, v___x_2382_, v_binderName_2364_, v___x_2381_, v_binderInfo_2367_, v___x_2385_);
v___x_2387_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2387_, 0, v_env_2374_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
lean_ctor_set(v___x_2387_, 2, v_lparams_2376_);
lean_ctor_set(v___x_2387_, 3, v___x_2384_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*4, v_safety_2377_);
lean_ctor_set_uint8(v___x_2387_, sizeof(void*)*4 + 1, v_allowPrimitive_2378_);
lean_inc_ref(v_stats_2353_);
v___x_2388_ = l_Lean4Lean_AddInductive_isRecArg(v_stats_2353_, v_binderType_2365_, v___x_2387_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___x_2387_);
lean_dec(v___x_2382_);
lean_dec(v_n_2370_);
lean_dec_ref(v_body_2366_);
lean_dec_ref(v_u_2358_);
lean_dec_ref(v_bu_2357_);
lean_dec(v_i_2356_);
lean_dec_ref(v_k_2354_);
lean_dec_ref(v_stats_2353_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
else
{
lean_object* v_a_2397_; lean_object* v___x_2398_; lean_object* v_bu_2399_; lean_object* v___y_2401_; 
v_a_2397_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2397_);
lean_dec_ref(v___x_2388_);
v___x_2398_ = l_Lean_Expr_fvar___override(v___x_2382_);
lean_inc_ref(v___x_2398_);
v_bu_2399_ = lean_array_push(v_bu_2357_, v___x_2398_);
if (lean_obj_tag(v_a_2397_) == 0)
{
v___y_2401_ = v_u_2358_;
goto v___jp_2400_;
}
else
{
lean_object* v___x_2405_; 
lean_dec_ref(v_a_2397_);
lean_inc_ref(v___x_2398_);
v___x_2405_ = lean_array_push(v_u_2358_, v___x_2398_);
v___y_2401_ = v___x_2405_;
goto v___jp_2400_;
}
v___jp_2400_:
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2402_ = lean_expr_instantiate1(v_body_2366_, v___x_2398_);
lean_dec_ref(v___x_2398_);
lean_dec_ref(v_body_2366_);
v___x_2403_ = lean_nat_add(v_i_2356_, v_one_2369_);
lean_dec(v_i_2356_);
v_t_2355_ = v___x_2402_;
v_i_2356_ = v___x_2403_;
v_bu_2357_ = v_bu_2399_;
v_u_2358_ = v___y_2401_;
v_x_2359_ = v_n_2370_;
v_a_2360_ = v___x_2387_;
goto _start;
}
}
}
else
{
lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v_binderType_2365_);
lean_dec(v_binderName_2364_);
v___x_2406_ = lean_array_fget_borrowed(v_params_2368_, v_i_2356_);
v___x_2407_ = lean_expr_instantiate1(v_body_2366_, v___x_2406_);
lean_dec_ref(v_body_2366_);
v___x_2408_ = lean_nat_add(v_i_2356_, v_one_2369_);
lean_dec(v_i_2356_);
v_t_2355_ = v___x_2407_;
v_i_2356_ = v___x_2408_;
v_x_2359_ = v_n_2370_;
goto _start;
}
}
else
{
lean_object* v___x_2410_; 
lean_dec(v_x_2359_);
lean_dec(v_i_2356_);
lean_dec_ref(v_stats_2353_);
v___x_2410_ = lean_apply_4(v_k_2354_, v_t_2355_, v_bu_2357_, v_u_2358_, v_a_2360_);
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop(lean_object* v_stats_2411_, lean_object* v_00_u03b1_2412_, lean_object* v_k_2413_, lean_object* v_t_2414_, lean_object* v_i_2415_, lean_object* v_bu_2416_, lean_object* v_u_2417_, lean_object* v_x_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v___x_2420_; 
lean_inc_ref(v_a_2419_);
v___x_2420_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop___redArg(v_stats_2411_, v_k_2413_, v_t_2414_, v_i_2415_, v_bu_2416_, v_u_2417_, v_x_2418_, v_a_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop___boxed(lean_object* v_stats_2421_, lean_object* v_00_u03b1_2422_, lean_object* v_k_2423_, lean_object* v_t_2424_, lean_object* v_i_2425_, lean_object* v_bu_2426_, lean_object* v_u_2427_, lean_object* v_x_2428_, lean_object* v_a_2429_){
_start:
{
lean_object* v_res_2430_; 
v_res_2430_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop(v_stats_2421_, v_00_u03b1_2422_, v_k_2423_, v_t_2424_, v_i_2425_, v_bu_2426_, v_u_2427_, v_x_2428_, v_a_2429_);
lean_dec_ref(v_a_2429_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg(lean_object* v_stats_2431_, lean_object* v_t_2432_, lean_object* v_k_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2435_ = lean_unsigned_to_nat(0u);
v___x_2436_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
v___x_2437_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v_a_2434_);
v___x_2438_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs_loop___redArg(v_stats_2431_, v_k_2433_, v_t_2432_, v___x_2435_, v___x_2436_, v___x_2436_, v___x_2437_, v_a_2434_);
return v___x_2438_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg___boxed(lean_object* v_stats_2439_, lean_object* v_t_2440_, lean_object* v_k_2441_, lean_object* v_a_2442_){
_start:
{
lean_object* v_res_2443_; 
v_res_2443_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg(v_stats_2439_, v_t_2440_, v_k_2441_, v_a_2442_);
lean_dec_ref(v_a_2442_);
return v_res_2443_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs(lean_object* v_stats_2444_, lean_object* v_00_u03b1_2445_, lean_object* v_t_2446_, lean_object* v_k_2447_, lean_object* v_a_2448_){
_start:
{
lean_object* v___x_2449_; 
v___x_2449_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg(v_stats_2444_, v_t_2446_, v_k_2447_, v_a_2448_);
return v___x_2449_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___boxed(lean_object* v_stats_2450_, lean_object* v_00_u03b1_2451_, lean_object* v_t_2452_, lean_object* v_k_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs(v_stats_2450_, v_00_u03b1_2451_, v_t_2452_, v_k_2453_, v_a_2454_);
lean_dec_ref(v_a_2454_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop___redArg(lean_object* v_k_2456_, lean_object* v_uiTy_2457_, lean_object* v_xs_2458_, lean_object* v_x_2459_, lean_object* v_a_2460_){
_start:
{
lean_object* v_zero_2461_; uint8_t v_isZero_2462_; 
v_zero_2461_ = lean_unsigned_to_nat(0u);
v_isZero_2462_ = lean_nat_dec_eq(v_x_2459_, v_zero_2461_);
if (v_isZero_2462_ == 1)
{
lean_object* v___x_2463_; 
lean_dec_ref(v_a_2460_);
lean_dec(v_x_2459_);
lean_dec_ref(v_xs_2458_);
lean_dec_ref(v_uiTy_2457_);
lean_dec_ref(v_k_2456_);
v___x_2463_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd_loop___redArg___closed__0));
return v___x_2463_;
}
else
{
if (lean_obj_tag(v_uiTy_2457_) == 7)
{
lean_object* v_ngen_2464_; lean_object* v_binderName_2465_; lean_object* v_binderType_2466_; lean_object* v_body_2467_; uint8_t v_binderInfo_2468_; lean_object* v_env_2469_; lean_object* v_lctx_2470_; lean_object* v_lparams_2471_; uint8_t v_safety_2472_; uint8_t v_allowPrimitive_2473_; lean_object* v_namePrefix_2474_; lean_object* v_idx_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; uint8_t v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_ngen_2464_ = lean_ctor_get(v_a_2460_, 3);
lean_inc_ref(v_ngen_2464_);
v_binderName_2465_ = lean_ctor_get(v_uiTy_2457_, 0);
lean_inc(v_binderName_2465_);
v_binderType_2466_ = lean_ctor_get(v_uiTy_2457_, 1);
lean_inc_ref(v_binderType_2466_);
v_body_2467_ = lean_ctor_get(v_uiTy_2457_, 2);
lean_inc_ref(v_body_2467_);
v_binderInfo_2468_ = lean_ctor_get_uint8(v_uiTy_2457_, sizeof(void*)*3 + 8);
lean_dec_ref(v_uiTy_2457_);
v_env_2469_ = lean_ctor_get(v_a_2460_, 0);
lean_inc_ref_n(v_env_2469_, 2);
v_lctx_2470_ = lean_ctor_get(v_a_2460_, 1);
lean_inc_ref(v_lctx_2470_);
v_lparams_2471_ = lean_ctor_get(v_a_2460_, 2);
lean_inc_n(v_lparams_2471_, 2);
v_safety_2472_ = lean_ctor_get_uint8(v_a_2460_, sizeof(void*)*4);
v_allowPrimitive_2473_ = lean_ctor_get_uint8(v_a_2460_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_2460_);
v_namePrefix_2474_ = lean_ctor_get(v_ngen_2464_, 0);
lean_inc_n(v_namePrefix_2474_, 2);
v_idx_2475_ = lean_ctor_get(v_ngen_2464_, 1);
lean_inc_n(v_idx_2475_, 2);
lean_dec_ref(v_ngen_2464_);
v___x_2476_ = lean_expr_consume_type_annotations(v_binderType_2466_);
v___x_2477_ = l_Lean_Name_num___override(v_namePrefix_2474_, v_idx_2475_);
v___x_2478_ = lean_unsigned_to_nat(1u);
v___x_2479_ = lean_nat_add(v_idx_2475_, v___x_2478_);
lean_dec(v_idx_2475_);
v___x_2480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2480_, 0, v_namePrefix_2474_);
lean_ctor_set(v___x_2480_, 1, v___x_2479_);
lean_inc(v___x_2477_);
v___x_2481_ = l_Lean_Expr_fvar___override(v___x_2477_);
v___x_2482_ = 0;
v___x_2483_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2470_, v___x_2477_, v_binderName_2465_, v___x_2476_, v_binderInfo_2468_, v___x_2482_);
lean_inc_ref(v___x_2483_);
v___x_2484_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2484_, 0, v_env_2469_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
lean_ctor_set(v___x_2484_, 2, v_lparams_2471_);
lean_ctor_set(v___x_2484_, 3, v___x_2480_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*4, v_safety_2472_);
lean_ctor_set_uint8(v___x_2484_, sizeof(void*)*4 + 1, v_allowPrimitive_2473_);
v___x_2485_ = lean_expr_instantiate1(v_body_2467_, v___x_2481_);
lean_dec_ref(v_body_2467_);
v___x_2486_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_2486_, 0, v___x_2485_);
v___x_2487_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_2469_, v_safety_2472_, v___x_2483_, v_lparams_2471_, v___x_2486_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec_ref(v___x_2484_);
lean_dec_ref(v___x_2481_);
lean_dec(v_x_2459_);
lean_dec_ref(v_xs_2458_);
lean_dec_ref(v_k_2456_);
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2487_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2487_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v_n_2497_; lean_object* v___x_2498_; 
v_a_2496_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2496_);
lean_dec_ref(v___x_2487_);
v_n_2497_ = lean_nat_sub(v_x_2459_, v___x_2478_);
lean_dec(v_x_2459_);
v___x_2498_ = lean_array_push(v_xs_2458_, v___x_2481_);
v_uiTy_2457_ = v_a_2496_;
v_xs_2458_ = v___x_2498_;
v_x_2459_ = v_n_2497_;
v_a_2460_ = v___x_2484_;
goto _start;
}
}
else
{
lean_object* v___x_2500_; 
lean_dec(v_x_2459_);
v___x_2500_ = lean_apply_3(v_k_2456_, v_uiTy_2457_, v_xs_2458_, v_a_2460_);
return v___x_2500_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop(lean_object* v_00_u03b1_2501_, lean_object* v_k_2502_, lean_object* v_uiTy_2503_, lean_object* v_xs_2504_, lean_object* v_x_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2507_; 
lean_inc_ref(v_a_2506_);
v___x_2507_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop___redArg(v_k_2502_, v_uiTy_2503_, v_xs_2504_, v_x_2505_, v_a_2506_);
return v___x_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop___boxed(lean_object* v_00_u03b1_2508_, lean_object* v_k_2509_, lean_object* v_uiTy_2510_, lean_object* v_xs_2511_, lean_object* v_x_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop(v_00_u03b1_2508_, v_k_2509_, v_uiTy_2510_, v_xs_2511_, v_x_2512_, v_a_2513_);
lean_dec_ref(v_a_2513_);
return v_res_2514_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg(lean_object* v_ui_2515_, lean_object* v_k_2516_, lean_object* v_a_2517_){
_start:
{
lean_object* v_env_2518_; lean_object* v_lctx_2519_; lean_object* v_lparams_2520_; uint8_t v_safety_2521_; lean_object* v___x_2522_; lean_object* v___x_2523_; 
v_env_2518_ = lean_ctor_get(v_a_2517_, 0);
v_lctx_2519_ = lean_ctor_get(v_a_2517_, 1);
v_lparams_2520_ = lean_ctor_get(v_a_2517_, 2);
v_safety_2521_ = lean_ctor_get_uint8(v_a_2517_, sizeof(void*)*4);
v___x_2522_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_inferType___boxed), 3, 1);
lean_closure_set(v___x_2522_, 0, v_ui_2515_);
lean_inc(v_lparams_2520_);
lean_inc_ref(v_lctx_2519_);
lean_inc_ref(v_env_2518_);
v___x_2523_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_2518_, v_safety_2521_, v_lctx_2519_, v_lparams_2520_, v___x_2522_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_k_2516_);
v_a_2524_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2523_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2523_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v_a_2532_ = lean_ctor_get(v___x_2523_, 0);
lean_inc(v_a_2532_);
lean_dec_ref(v___x_2523_);
v___x_2533_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_whnf___boxed), 3, 1);
lean_closure_set(v___x_2533_, 0, v_a_2532_);
lean_inc(v_lparams_2520_);
lean_inc_ref(v_lctx_2519_);
lean_inc_ref(v_env_2518_);
v___x_2534_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_2518_, v_safety_2521_, v_lctx_2519_, v_lparams_2520_, v___x_2533_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec_ref(v_k_2516_);
v_a_2535_ = lean_ctor_get(v___x_2534_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2534_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2534_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2534_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
v_a_2543_ = lean_ctor_get(v___x_2534_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2534_);
v___x_2544_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
v___x_2545_ = lean_unsigned_to_nat(1000u);
lean_inc_ref(v_a_2517_);
v___x_2546_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs_loop___redArg(v_k_2516_, v_a_2543_, v___x_2544_, v___x_2545_, v_a_2517_);
return v___x_2546_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg___boxed(lean_object* v_ui_2547_, lean_object* v_k_2548_, lean_object* v_a_2549_){
_start:
{
lean_object* v_res_2550_; 
v_res_2550_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg(v_ui_2547_, v_k_2548_, v_a_2549_);
lean_dec_ref(v_a_2549_);
return v_res_2550_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs(lean_object* v_00_u03b1_2551_, lean_object* v_ui_2552_, lean_object* v_k_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg(v_ui_2552_, v_k_2553_, v_a_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___boxed(lean_object* v_00_u03b1_2556_, lean_object* v_ui_2557_, lean_object* v_k_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs(v_00_u03b1_2556_, v_ui_2557_, v_k_2558_, v_a_2559_);
lean_dec_ref(v_a_2559_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___lam__0(lean_object* v_stats_2561_, lean_object* v_recInfos_2562_, lean_object* v_ui_2563_, uint8_t v___x_2564_, lean_object* v_uiTy_2565_, lean_object* v_xs_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___y_2569_; lean_object* v___x_2591_; 
lean_inc_ref(v_uiTy_2565_);
lean_inc_ref(v_stats_2561_);
v___x_2591_ = l_Lean4Lean_AddInductive_isValidIndApp_x3f(v_stats_2561_, v_uiTy_2565_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v___x_2592_; lean_object* v___x_2593_; 
v___x_2592_ = lean_obj_once(&l_Lean4Lean_AddInductive_getIIndices___closed__3, &l_Lean4Lean_AddInductive_getIIndices___closed__3_once, _init_l_Lean4Lean_AddInductive_getIIndices___closed__3);
v___x_2593_ = l_panic___at___00Lean4Lean_AddInductive_declareConstructors_spec__0(v___x_2592_);
v___y_2569_ = v___x_2593_;
goto v___jp_2568_;
}
else
{
lean_object* v_val_2594_; 
v_val_2594_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_val_2594_);
lean_dec_ref(v___x_2591_);
v___y_2569_ = v_val_2594_;
goto v___jp_2568_;
}
v___jp_2568_:
{
lean_object* v_params_2570_; lean_object* v_nargs_2571_; lean_object* v_lctx_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v_motive_2575_; lean_object* v_dummy_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v_a_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; uint8_t v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; 
v_params_2570_ = lean_ctor_get(v_stats_2561_, 5);
lean_inc_ref(v_params_2570_);
lean_dec_ref(v_stats_2561_);
v_nargs_2571_ = l_Lean_Expr_getAppNumArgs(v_uiTy_2565_);
v_lctx_2572_ = lean_ctor_get(v___y_2567_, 1);
v___x_2573_ = l_Lean4Lean_AddInductive_instInhabitedRecInfo_default;
v___x_2574_ = lean_array_get_borrowed(v___x_2573_, v_recInfos_2562_, v___y_2569_);
lean_dec(v___y_2569_);
v_motive_2575_ = lean_ctor_get(v___x_2574_, 0);
v_dummy_2576_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
lean_inc(v_nargs_2571_);
v___x_2577_ = lean_mk_array(v_nargs_2571_, v_dummy_2576_);
v___x_2578_ = lean_unsigned_to_nat(1u);
v___x_2579_ = lean_nat_sub(v_nargs_2571_, v___x_2578_);
lean_dec(v_nargs_2571_);
v_a_2580_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_uiTy_2565_, v___x_2577_, v___x_2579_);
v___x_2581_ = lean_array_get_size(v_a_2580_);
v___x_2582_ = lean_array_get_size(v_params_2570_);
lean_dec_ref(v_params_2570_);
v___x_2583_ = l_Array_toSubarray___redArg(v_a_2580_, v___x_2582_, v___x_2581_);
v___x_2584_ = l_Subarray_copy___redArg(v___x_2583_);
lean_inc_ref(v_motive_2575_);
v___x_2585_ = l_Lean_mkAppN(v_motive_2575_, v___x_2584_);
lean_dec_ref(v___x_2584_);
v___x_2586_ = l_Lean_mkAppN(v_ui_2563_, v_xs_2566_);
v___x_2587_ = l_Lean_Expr_app___override(v___x_2585_, v___x_2586_);
v___x_2588_ = 0;
lean_inc_ref(v_lctx_2572_);
v___x_2589_ = l_Lean_LocalContext_mkForall(v_lctx_2572_, v_xs_2566_, v___x_2587_, v___x_2564_, v___x_2588_);
lean_dec_ref(v___x_2587_);
v___x_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
return v___x_2590_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___lam__0___boxed(lean_object* v_stats_2595_, lean_object* v_recInfos_2596_, lean_object* v_ui_2597_, lean_object* v___x_2598_, lean_object* v_uiTy_2599_, lean_object* v_xs_2600_, lean_object* v___y_2601_){
_start:
{
uint8_t v___x_1089__boxed_2602_; lean_object* v_res_2603_; 
v___x_1089__boxed_2602_ = lean_unbox(v___x_2598_);
v_res_2603_ = l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___lam__0(v_stats_2595_, v_recInfos_2596_, v_ui_2597_, v___x_1089__boxed_2602_, v_uiTy_2599_, v_xs_2600_, v___y_2601_);
lean_dec_ref(v___y_2601_);
lean_dec_ref(v_xs_2600_);
lean_dec_ref(v_recInfos_2596_);
return v_res_2603_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg(lean_object* v_stats_2605_, lean_object* v_u_2606_, lean_object* v_recInfos_2607_, lean_object* v_i_2608_, lean_object* v_v_2609_, lean_object* v_k_2610_, lean_object* v_a_2611_){
_start:
{
lean_object* v___x_2612_; uint8_t v___x_2613_; 
v___x_2612_ = lean_array_get_size(v_u_2606_);
v___x_2613_ = lean_nat_dec_lt(v_i_2608_, v___x_2612_);
if (v___x_2613_ == 0)
{
lean_object* v___x_2614_; 
lean_dec(v_i_2608_);
lean_dec_ref(v_recInfos_2607_);
lean_dec_ref(v_stats_2605_);
v___x_2614_ = lean_apply_2(v_k_2610_, v_v_2609_, v_a_2611_);
return v___x_2614_;
}
else
{
lean_object* v_ui_2615_; lean_object* v___x_2616_; lean_object* v___f_2617_; lean_object* v___x_2618_; 
v_ui_2615_ = lean_array_fget_borrowed(v_u_2606_, v_i_2608_);
v___x_2616_ = lean_box(v___x_2613_);
lean_inc_n(v_ui_2615_, 2);
lean_inc_ref(v_recInfos_2607_);
lean_inc_ref(v_stats_2605_);
v___f_2617_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___lam__0___boxed), 7, 4);
lean_closure_set(v___f_2617_, 0, v_stats_2605_);
lean_closure_set(v___f_2617_, 1, v_recInfos_2607_);
lean_closure_set(v___f_2617_, 2, v_ui_2615_);
lean_closure_set(v___f_2617_, 3, v___x_2616_);
v___x_2618_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg(v_ui_2615_, v___f_2617_, v_a_2611_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec_ref(v_a_2611_);
lean_dec_ref(v_k_2610_);
lean_dec_ref(v_v_2609_);
lean_dec(v_i_2608_);
lean_dec_ref(v_recInfos_2607_);
lean_dec_ref(v_stats_2605_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2618_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2618_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
else
{
lean_object* v_ngen_2627_; lean_object* v_a_2628_; lean_object* v_env_2629_; lean_object* v_lctx_2630_; lean_object* v_lparams_2631_; uint8_t v_safety_2632_; uint8_t v_allowPrimitive_2633_; lean_object* v_namePrefix_2634_; lean_object* v_idx_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; uint8_t v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v_ngen_2627_ = lean_ctor_get(v_a_2611_, 3);
lean_inc_ref(v_ngen_2627_);
v_a_2628_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2628_);
lean_dec_ref(v___x_2618_);
v_env_2629_ = lean_ctor_get(v_a_2611_, 0);
lean_inc_ref(v_env_2629_);
v_lctx_2630_ = lean_ctor_get(v_a_2611_, 1);
lean_inc_ref_n(v_lctx_2630_, 2);
v_lparams_2631_ = lean_ctor_get(v_a_2611_, 2);
lean_inc(v_lparams_2631_);
v_safety_2632_ = lean_ctor_get_uint8(v_a_2611_, sizeof(void*)*4);
v_allowPrimitive_2633_ = lean_ctor_get_uint8(v_a_2611_, sizeof(void*)*4 + 1);
lean_dec_ref(v_a_2611_);
v_namePrefix_2634_ = lean_ctor_get(v_ngen_2627_, 0);
lean_inc_n(v_namePrefix_2634_, 2);
v_idx_2635_ = lean_ctor_get(v_ngen_2627_, 1);
lean_inc_n(v_idx_2635_, 2);
lean_dec_ref(v_ngen_2627_);
v___x_2636_ = l_Lean_Expr_fvarId_x21(v_ui_2615_);
v___x_2637_ = l_Lean_LocalContext_get_x21(v_lctx_2630_, v___x_2636_);
v___x_2638_ = l_Lean_LocalDecl_userName(v___x_2637_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = ((lean_object*)(l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___closed__0));
v___x_2640_ = lean_name_append_after(v___x_2638_, v___x_2639_);
v___x_2641_ = 0;
v___x_2642_ = lean_expr_consume_type_annotations(v_a_2628_);
v___x_2643_ = l_Lean_Name_num___override(v_namePrefix_2634_, v_idx_2635_);
v___x_2644_ = lean_unsigned_to_nat(1u);
v___x_2645_ = lean_nat_add(v_idx_2635_, v___x_2644_);
lean_dec(v_idx_2635_);
v___x_2646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2646_, 0, v_namePrefix_2634_);
lean_ctor_set(v___x_2646_, 1, v___x_2645_);
lean_inc(v___x_2643_);
v___x_2647_ = l_Lean_Expr_fvar___override(v___x_2643_);
v___x_2648_ = 0;
v___x_2649_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2630_, v___x_2643_, v___x_2640_, v___x_2642_, v___x_2641_, v___x_2648_);
v___x_2650_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2650_, 0, v_env_2629_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
lean_ctor_set(v___x_2650_, 2, v_lparams_2631_);
lean_ctor_set(v___x_2650_, 3, v___x_2646_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*4, v_safety_2632_);
lean_ctor_set_uint8(v___x_2650_, sizeof(void*)*4 + 1, v_allowPrimitive_2633_);
v___x_2651_ = lean_nat_add(v_i_2608_, v___x_2644_);
lean_dec(v_i_2608_);
v___x_2652_ = lean_array_push(v_v_2609_, v___x_2647_);
v_i_2608_ = v___x_2651_;
v_v_2609_ = v___x_2652_;
v_a_2611_ = v___x_2650_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg___boxed(lean_object* v_stats_2654_, lean_object* v_u_2655_, lean_object* v_recInfos_2656_, lean_object* v_i_2657_, lean_object* v_v_2658_, lean_object* v_k_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg(v_stats_2654_, v_u_2655_, v_recInfos_2656_, v_i_2657_, v_v_2658_, v_k_2659_, v_a_2660_);
lean_dec_ref(v_u_2655_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU(lean_object* v_stats_2662_, lean_object* v_u_2663_, lean_object* v_recInfos_2664_, lean_object* v_00_u03b1_2665_, lean_object* v_i_2666_, lean_object* v_v_2667_, lean_object* v_k_2668_, lean_object* v_a_2669_){
_start:
{
lean_object* v___x_2670_; 
lean_inc_ref(v_a_2669_);
v___x_2670_ = l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg(v_stats_2662_, v_u_2663_, v_recInfos_2664_, v_i_2666_, v_v_2667_, v_k_2668_, v_a_2669_);
return v___x_2670_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopU___boxed(lean_object* v_stats_2671_, lean_object* v_u_2672_, lean_object* v_recInfos_2673_, lean_object* v_00_u03b1_2674_, lean_object* v_i_2675_, lean_object* v_v_2676_, lean_object* v_k_2677_, lean_object* v_a_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lean4Lean_AddInductive_mkRecInfos_loopU(v_stats_2671_, v_u_2672_, v_recInfos_2673_, v_00_u03b1_2674_, v_i_2675_, v_v_2676_, v_k_2677_, v_a_2678_);
lean_dec_ref(v_a_2678_);
lean_dec_ref(v_u_2672_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Inductive_Add_0__Lean4Lean_AddInductive_mkRecInfos_loopU_match__1_splitter___redArg(lean_object* v_x_2680_, lean_object* v_h__1_2681_){
_start:
{
lean_object* v_fst_2682_; lean_object* v_snd_2683_; lean_object* v___x_2684_; 
v_fst_2682_ = lean_ctor_get(v_x_2680_, 0);
lean_inc(v_fst_2682_);
v_snd_2683_ = lean_ctor_get(v_x_2680_, 1);
lean_inc(v_snd_2683_);
lean_dec_ref(v_x_2680_);
v___x_2684_ = lean_apply_2(v_h__1_2681_, v_fst_2682_, v_snd_2683_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_Inductive_Add_0__Lean4Lean_AddInductive_mkRecInfos_loopU_match__1_splitter(lean_object* v_motive_2685_, lean_object* v_x_2686_, lean_object* v_h__1_2687_){
_start:
{
lean_object* v_fst_2688_; lean_object* v_snd_2689_; lean_object* v___x_2690_; 
v_fst_2688_ = lean_ctor_get(v_x_2686_, 0);
lean_inc(v_fst_2688_);
v_snd_2689_ = lean_ctor_get(v_x_2686_, 1);
lean_inc(v_snd_2689_);
lean_dec_ref(v_x_2686_);
v___x_2690_ = lean_apply_2(v_h__1_2687_, v_fst_2688_, v_snd_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__0(lean_object* v_motiveApp_2691_, lean_object* v_bu_2692_, lean_object* v_name_2693_, lean_object* v_indTypeName_2694_, lean_object* v___x_2695_, lean_object* v_recInfos_2696_, lean_object* v_dIdx_2697_, lean_object* v_stats_2698_, lean_object* v_tail_2699_, lean_object* v_k_2700_, lean_object* v_v_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_ngen_2703_; lean_object* v_env_2704_; lean_object* v_lctx_2705_; lean_object* v_lparams_2706_; uint8_t v_safety_2707_; uint8_t v_allowPrimitive_2708_; lean_object* v_namePrefix_2709_; lean_object* v_idx_2710_; uint8_t v___x_2711_; uint8_t v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; 
v_ngen_2703_ = lean_ctor_get(v___y_2702_, 3);
v_env_2704_ = lean_ctor_get(v___y_2702_, 0);
v_lctx_2705_ = lean_ctor_get(v___y_2702_, 1);
v_lparams_2706_ = lean_ctor_get(v___y_2702_, 2);
v_safety_2707_ = lean_ctor_get_uint8(v___y_2702_, sizeof(void*)*4);
v_allowPrimitive_2708_ = lean_ctor_get_uint8(v___y_2702_, sizeof(void*)*4 + 1);
v_namePrefix_2709_ = lean_ctor_get(v_ngen_2703_, 0);
v_idx_2710_ = lean_ctor_get(v_ngen_2703_, 1);
v___x_2711_ = 1;
v___x_2712_ = 0;
lean_inc_ref_n(v_lctx_2705_, 3);
v___x_2713_ = l_Lean_LocalContext_mkForall(v_lctx_2705_, v_v_2701_, v_motiveApp_2691_, v___x_2711_, v___x_2712_);
v___x_2714_ = l_Lean_LocalContext_mkForall(v_lctx_2705_, v_bu_2692_, v___x_2713_, v___x_2711_, v___x_2712_);
lean_dec_ref(v___x_2713_);
v___x_2715_ = lean_box(0);
v___x_2716_ = l_Lean_Name_replacePrefix(v_name_2693_, v_indTypeName_2694_, v___x_2715_);
v___x_2717_ = 0;
v___x_2718_ = lean_expr_consume_type_annotations(v___x_2714_);
lean_inc(v_idx_2710_);
lean_inc_n(v_namePrefix_2709_, 2);
v___x_2719_ = l_Lean_Name_num___override(v_namePrefix_2709_, v_idx_2710_);
v___x_2720_ = lean_nat_add(v_idx_2710_, v___x_2695_);
v___x_2721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2721_, 0, v_namePrefix_2709_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = 0;
lean_inc(v___x_2719_);
v___x_2723_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_2705_, v___x_2719_, v___x_2716_, v___x_2718_, v___x_2717_, v___x_2722_);
lean_inc(v_lparams_2706_);
lean_inc_ref(v_env_2704_);
v___x_2724_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_2724_, 0, v_env_2704_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
lean_ctor_set(v___x_2724_, 2, v_lparams_2706_);
lean_ctor_set(v___x_2724_, 3, v___x_2721_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*4, v_safety_2707_);
lean_ctor_set_uint8(v___x_2724_, sizeof(void*)*4 + 1, v_allowPrimitive_2708_);
v___x_2725_ = lean_array_get_size(v_recInfos_2696_);
v___x_2726_ = lean_nat_dec_lt(v_dIdx_2697_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
lean_dec(v___x_2719_);
v___x_2727_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg(v_stats_2698_, v_indTypeName_2694_, v_dIdx_2697_, v_recInfos_2696_, v_tail_2699_, v_k_2700_, v___x_2724_);
lean_dec_ref(v___x_2724_);
return v___x_2727_;
}
else
{
lean_object* v_v_2728_; lean_object* v_motive_2729_; lean_object* v_minors_2730_; lean_object* v_indices_2731_; lean_object* v_major_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2745_; 
v_v_2728_ = lean_array_fget(v_recInfos_2696_, v_dIdx_2697_);
v_motive_2729_ = lean_ctor_get(v_v_2728_, 0);
v_minors_2730_ = lean_ctor_get(v_v_2728_, 1);
v_indices_2731_ = lean_ctor_get(v_v_2728_, 2);
v_major_2732_ = lean_ctor_get(v_v_2728_, 3);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_v_2728_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2734_ = v_v_2728_;
v_isShared_2735_ = v_isSharedCheck_2745_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_major_2732_);
lean_inc(v_indices_2731_);
lean_inc(v_minors_2730_);
lean_inc(v_motive_2729_);
lean_dec(v_v_2728_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2745_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v_xs_x27_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2736_ = l_Lean_Expr_fvar___override(v___x_2719_);
v___x_2737_ = lean_box(0);
v_xs_x27_2738_ = lean_array_fset(v_recInfos_2696_, v_dIdx_2697_, v___x_2737_);
v___x_2739_ = lean_array_push(v_minors_2730_, v___x_2736_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set(v___x_2734_, 1, v___x_2739_);
v___x_2741_ = v___x_2734_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_motive_2729_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2744_, 2, v_indices_2731_);
lean_ctor_set(v_reuseFailAlloc_2744_, 3, v_major_2732_);
v___x_2741_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
lean_object* v___x_2742_; lean_object* v___x_2743_; 
v___x_2742_ = lean_array_fset(v_xs_x27_2738_, v_dIdx_2697_, v___x_2741_);
v___x_2743_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg(v_stats_2698_, v_indTypeName_2694_, v_dIdx_2697_, v___x_2742_, v_tail_2699_, v_k_2700_, v___x_2724_);
lean_dec_ref(v___x_2724_);
return v___x_2743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__0___boxed(lean_object* v_motiveApp_2746_, lean_object* v_bu_2747_, lean_object* v_name_2748_, lean_object* v_indTypeName_2749_, lean_object* v___x_2750_, lean_object* v_recInfos_2751_, lean_object* v_dIdx_2752_, lean_object* v_stats_2753_, lean_object* v_tail_2754_, lean_object* v_k_2755_, lean_object* v_v_2756_, lean_object* v___y_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__0(v_motiveApp_2746_, v_bu_2747_, v_name_2748_, v_indTypeName_2749_, v___x_2750_, v_recInfos_2751_, v_dIdx_2752_, v_stats_2753_, v_tail_2754_, v_k_2755_, v_v_2756_, v___y_2757_);
lean_dec_ref(v___y_2757_);
lean_dec_ref(v_v_2756_);
lean_dec(v___x_2750_);
lean_dec_ref(v_bu_2747_);
lean_dec_ref(v_motiveApp_2746_);
return v_res_2758_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__1(lean_object* v_stats_2759_, lean_object* v___x_2760_, lean_object* v_recInfos_2761_, lean_object* v_name_2762_, lean_object* v_indTypeName_2763_, lean_object* v_dIdx_2764_, lean_object* v_tail_2765_, lean_object* v_k_2766_, lean_object* v_t_2767_, lean_object* v_bu_2768_, lean_object* v_u_2769_, lean_object* v___y_2770_){
_start:
{
lean_object* v___y_2772_; lean_object* v___x_2796_; 
lean_inc_ref(v_t_2767_);
lean_inc_ref(v_stats_2759_);
v___x_2796_ = l_Lean4Lean_AddInductive_isValidIndApp_x3f(v_stats_2759_, v_t_2767_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_obj_once(&l_Lean4Lean_AddInductive_getIIndices___closed__3, &l_Lean4Lean_AddInductive_getIIndices___closed__3_once, _init_l_Lean4Lean_AddInductive_getIIndices___closed__3);
v___x_2798_ = l_panic___at___00Lean4Lean_AddInductive_declareConstructors_spec__0(v___x_2797_);
v___y_2772_ = v___x_2798_;
goto v___jp_2771_;
}
else
{
lean_object* v_val_2799_; 
v_val_2799_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_val_2799_);
lean_dec_ref(v___x_2796_);
v___y_2772_ = v_val_2799_;
goto v___jp_2771_;
}
v___jp_2771_:
{
lean_object* v_levels_2773_; lean_object* v_params_2774_; lean_object* v___x_2775_; lean_object* v_motive_2776_; lean_object* v_nargs_2777_; lean_object* v_dummy_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v_a_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v_introApp_2789_; lean_object* v___x_2790_; lean_object* v_motiveApp_2791_; lean_object* v___f_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_levels_2773_ = lean_ctor_get(v_stats_2759_, 1);
v_params_2774_ = lean_ctor_get(v_stats_2759_, 5);
v___x_2775_ = lean_array_get_borrowed(v___x_2760_, v_recInfos_2761_, v___y_2772_);
lean_dec(v___y_2772_);
v_motive_2776_ = lean_ctor_get(v___x_2775_, 0);
v_nargs_2777_ = l_Lean_Expr_getAppNumArgs(v_t_2767_);
v_dummy_2778_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
lean_inc(v_nargs_2777_);
v___x_2779_ = lean_mk_array(v_nargs_2777_, v_dummy_2778_);
v___x_2780_ = lean_unsigned_to_nat(1u);
v___x_2781_ = lean_nat_sub(v_nargs_2777_, v___x_2780_);
lean_dec(v_nargs_2777_);
v_a_2782_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_2767_, v___x_2779_, v___x_2781_);
v___x_2783_ = lean_array_get_size(v_a_2782_);
v___x_2784_ = lean_array_get_size(v_params_2774_);
v___x_2785_ = l_Array_toSubarray___redArg(v_a_2782_, v___x_2784_, v___x_2783_);
v___x_2786_ = l_Subarray_copy___redArg(v___x_2785_);
lean_inc(v_levels_2773_);
lean_inc(v_name_2762_);
v___x_2787_ = l_Lean_Expr_const___override(v_name_2762_, v_levels_2773_);
v___x_2788_ = l_Lean_mkAppN(v___x_2787_, v_params_2774_);
v_introApp_2789_ = l_Lean_mkAppN(v___x_2788_, v_bu_2768_);
lean_inc_ref(v_motive_2776_);
v___x_2790_ = l_Lean_mkAppN(v_motive_2776_, v___x_2786_);
lean_dec_ref(v___x_2786_);
v_motiveApp_2791_ = l_Lean_Expr_app___override(v___x_2790_, v_introApp_2789_);
lean_inc_ref(v_stats_2759_);
lean_inc_ref(v_recInfos_2761_);
v___f_2792_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__0___boxed), 12, 10);
lean_closure_set(v___f_2792_, 0, v_motiveApp_2791_);
lean_closure_set(v___f_2792_, 1, v_bu_2768_);
lean_closure_set(v___f_2792_, 2, v_name_2762_);
lean_closure_set(v___f_2792_, 3, v_indTypeName_2763_);
lean_closure_set(v___f_2792_, 4, v___x_2780_);
lean_closure_set(v___f_2792_, 5, v_recInfos_2761_);
lean_closure_set(v___f_2792_, 6, v_dIdx_2764_);
lean_closure_set(v___f_2792_, 7, v_stats_2759_);
lean_closure_set(v___f_2792_, 8, v_tail_2765_);
lean_closure_set(v___f_2792_, 9, v_k_2766_);
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
lean_inc_ref(v___y_2770_);
v___x_2795_ = l_Lean4Lean_AddInductive_mkRecInfos_loopU___redArg(v_stats_2759_, v_u_2769_, v_recInfos_2761_, v___x_2793_, v___x_2794_, v___f_2792_, v___y_2770_);
return v___x_2795_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__1___boxed(lean_object* v_stats_2800_, lean_object* v___x_2801_, lean_object* v_recInfos_2802_, lean_object* v_name_2803_, lean_object* v_indTypeName_2804_, lean_object* v_dIdx_2805_, lean_object* v_tail_2806_, lean_object* v_k_2807_, lean_object* v_t_2808_, lean_object* v_bu_2809_, lean_object* v_u_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__1(v_stats_2800_, v___x_2801_, v_recInfos_2802_, v_name_2803_, v_indTypeName_2804_, v_dIdx_2805_, v_tail_2806_, v_k_2807_, v_t_2808_, v_bu_2809_, v_u_2810_, v___y_2811_);
lean_dec_ref(v___y_2811_);
lean_dec_ref(v_u_2810_);
lean_dec_ref(v___x_2801_);
return v_res_2812_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg(lean_object* v_stats_2813_, lean_object* v_indTypeName_2814_, lean_object* v_dIdx_2815_, lean_object* v_recInfos_2816_, lean_object* v_ctors_2817_, lean_object* v_k_2818_, lean_object* v_a_2819_){
_start:
{
if (lean_obj_tag(v_ctors_2817_) == 0)
{
lean_object* v___x_2820_; 
lean_dec(v_dIdx_2815_);
lean_dec(v_indTypeName_2814_);
lean_dec_ref(v_stats_2813_);
lean_inc_ref(v_a_2819_);
v___x_2820_ = lean_apply_2(v_k_2818_, v_recInfos_2816_, v_a_2819_);
return v___x_2820_;
}
else
{
lean_object* v_head_2821_; lean_object* v_tail_2822_; lean_object* v_name_2823_; lean_object* v_type_2824_; lean_object* v___x_2825_; lean_object* v___f_2826_; lean_object* v___x_2827_; 
v_head_2821_ = lean_ctor_get(v_ctors_2817_, 0);
lean_inc(v_head_2821_);
v_tail_2822_ = lean_ctor_get(v_ctors_2817_, 1);
lean_inc(v_tail_2822_);
lean_dec_ref(v_ctors_2817_);
v_name_2823_ = lean_ctor_get(v_head_2821_, 0);
lean_inc(v_name_2823_);
v_type_2824_ = lean_ctor_get(v_head_2821_, 1);
lean_inc_ref(v_type_2824_);
lean_dec(v_head_2821_);
v___x_2825_ = l_Lean4Lean_AddInductive_instInhabitedRecInfo_default;
lean_inc_ref(v_stats_2813_);
v___f_2826_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___lam__1___boxed), 12, 8);
lean_closure_set(v___f_2826_, 0, v_stats_2813_);
lean_closure_set(v___f_2826_, 1, v___x_2825_);
lean_closure_set(v___f_2826_, 2, v_recInfos_2816_);
lean_closure_set(v___f_2826_, 3, v_name_2823_);
lean_closure_set(v___f_2826_, 4, v_indTypeName_2814_);
lean_closure_set(v___f_2826_, 5, v_dIdx_2815_);
lean_closure_set(v___f_2826_, 6, v_tail_2822_);
lean_closure_set(v___f_2826_, 7, v_k_2818_);
v___x_2827_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg(v_stats_2813_, v_type_2824_, v___f_2826_, v_a_2819_);
return v___x_2827_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg___boxed(lean_object* v_stats_2828_, lean_object* v_indTypeName_2829_, lean_object* v_dIdx_2830_, lean_object* v_recInfos_2831_, lean_object* v_ctors_2832_, lean_object* v_k_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg(v_stats_2828_, v_indTypeName_2829_, v_dIdx_2830_, v_recInfos_2831_, v_ctors_2832_, v_k_2833_, v_a_2834_);
lean_dec_ref(v_a_2834_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors(lean_object* v_stats_2836_, lean_object* v_indTypeName_2837_, lean_object* v_dIdx_2838_, lean_object* v_00_u03b1_2839_, lean_object* v_recInfos_2840_, lean_object* v_ctors_2841_, lean_object* v_k_2842_, lean_object* v_a_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg(v_stats_2836_, v_indTypeName_2837_, v_dIdx_2838_, v_recInfos_2840_, v_ctors_2841_, v_k_2842_, v_a_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___boxed(lean_object* v_stats_2845_, lean_object* v_indTypeName_2846_, lean_object* v_dIdx_2847_, lean_object* v_00_u03b1_2848_, lean_object* v_recInfos_2849_, lean_object* v_ctors_2850_, lean_object* v_k_2851_, lean_object* v_a_2852_){
_start:
{
lean_object* v_res_2853_; 
v_res_2853_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors(v_stats_2845_, v_indTypeName_2846_, v_dIdx_2847_, v_00_u03b1_2848_, v_recInfos_2849_, v_ctors_2850_, v_k_2851_, v_a_2852_);
lean_dec_ref(v_a_2852_);
return v_res_2853_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___lam__0___boxed(lean_object* v_dIdx_2854_, lean_object* v_stats_2855_, lean_object* v_indTypes_2856_, lean_object* v_k_2857_, lean_object* v_recInfos_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_res_2860_; 
v_res_2860_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___lam__0(v_dIdx_2854_, v_stats_2855_, v_indTypes_2856_, v_k_2857_, v_recInfos_2858_, v___y_2859_);
lean_dec_ref(v___y_2859_);
lean_dec(v_dIdx_2854_);
return v_res_2860_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg(lean_object* v_stats_2861_, lean_object* v_indTypes_2862_, lean_object* v_dIdx_2863_, lean_object* v_recInfos_2864_, lean_object* v_k_2865_, lean_object* v_a_2866_){
_start:
{
lean_object* v___x_2867_; uint8_t v___x_2868_; 
v___x_2867_ = lean_array_get_size(v_indTypes_2862_);
v___x_2868_ = lean_nat_dec_lt(v_dIdx_2863_, v___x_2867_);
if (v___x_2868_ == 0)
{
lean_object* v___x_2869_; 
lean_dec(v_dIdx_2863_);
lean_dec_ref(v_indTypes_2862_);
lean_dec_ref(v_stats_2861_);
lean_inc_ref(v_a_2866_);
v___x_2869_ = lean_apply_2(v_k_2865_, v_recInfos_2864_, v_a_2866_);
return v___x_2869_;
}
else
{
lean_object* v_indType_2870_; lean_object* v_name_2871_; lean_object* v_ctors_2872_; lean_object* v___f_2873_; lean_object* v___x_2874_; 
v_indType_2870_ = lean_array_fget_borrowed(v_indTypes_2862_, v_dIdx_2863_);
v_name_2871_ = lean_ctor_get(v_indType_2870_, 0);
lean_inc(v_name_2871_);
v_ctors_2872_ = lean_ctor_get(v_indType_2870_, 2);
lean_inc(v_ctors_2872_);
lean_inc_ref(v_stats_2861_);
lean_inc(v_dIdx_2863_);
v___f_2873_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2873_, 0, v_dIdx_2863_);
lean_closure_set(v___f_2873_, 1, v_stats_2861_);
lean_closure_set(v___f_2873_, 2, v_indTypes_2862_);
lean_closure_set(v___f_2873_, 3, v_k_2865_);
v___x_2874_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtors___redArg(v_stats_2861_, v_name_2871_, v_dIdx_2863_, v_recInfos_2864_, v_ctors_2872_, v___f_2873_, v_a_2866_);
return v___x_2874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___lam__0(lean_object* v_dIdx_2875_, lean_object* v_stats_2876_, lean_object* v_indTypes_2877_, lean_object* v_k_2878_, lean_object* v_recInfos_2879_, lean_object* v___y_2880_){
_start:
{
lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; 
v___x_2881_ = lean_unsigned_to_nat(1u);
v___x_2882_ = lean_nat_add(v_dIdx_2875_, v___x_2881_);
v___x_2883_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg(v_stats_2876_, v_indTypes_2877_, v___x_2882_, v_recInfos_2879_, v_k_2878_, v___y_2880_);
return v___x_2883_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg___boxed(lean_object* v_stats_2884_, lean_object* v_indTypes_2885_, lean_object* v_dIdx_2886_, lean_object* v_recInfos_2887_, lean_object* v_k_2888_, lean_object* v_a_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg(v_stats_2884_, v_indTypes_2885_, v_dIdx_2886_, v_recInfos_2887_, v_k_2888_, v_a_2889_);
lean_dec_ref(v_a_2889_);
return v_res_2890_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2(lean_object* v_stats_2891_, lean_object* v_indTypes_2892_, lean_object* v_00_u03b1_2893_, lean_object* v_dIdx_2894_, lean_object* v_recInfos_2895_, lean_object* v_k_2896_, lean_object* v_a_2897_){
_start:
{
lean_object* v___x_2898_; 
v___x_2898_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg(v_stats_2891_, v_indTypes_2892_, v_dIdx_2894_, v_recInfos_2895_, v_k_2896_, v_a_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___boxed(lean_object* v_stats_2899_, lean_object* v_indTypes_2900_, lean_object* v_00_u03b1_2901_, lean_object* v_dIdx_2902_, lean_object* v_recInfos_2903_, lean_object* v_k_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd2(v_stats_2899_, v_indTypes_2900_, v_00_u03b1_2901_, v_dIdx_2902_, v_recInfos_2903_, v_k_2904_, v_a_2905_);
lean_dec_ref(v_a_2905_);
return v_res_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg___lam__0(lean_object* v_stats_2907_, lean_object* v_indTypes_2908_, lean_object* v___x_2909_, lean_object* v_k_2910_, lean_object* v_recInfos_2911_, lean_object* v___y_2912_){
_start:
{
lean_object* v___x_2913_; 
v___x_2913_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd2___redArg(v_stats_2907_, v_indTypes_2908_, v___x_2909_, v_recInfos_2911_, v_k_2910_, v___y_2912_);
return v___x_2913_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg___lam__0___boxed(lean_object* v_stats_2914_, lean_object* v_indTypes_2915_, lean_object* v___x_2916_, lean_object* v_k_2917_, lean_object* v_recInfos_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l_Lean4Lean_AddInductive_mkRecInfos___redArg___lam__0(v_stats_2914_, v_indTypes_2915_, v___x_2916_, v_k_2917_, v_recInfos_2918_, v___y_2919_);
lean_dec_ref(v___y_2919_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg(lean_object* v_stats_2923_, lean_object* v_indTypes_2924_, lean_object* v_elimLevel_2925_, lean_object* v_k_2926_, lean_object* v_a_2927_){
_start:
{
lean_object* v___x_2928_; lean_object* v___f_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_indTypes_2924_);
lean_inc_ref(v_stats_2923_);
v___f_2929_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_mkRecInfos___redArg___lam__0___boxed), 6, 4);
lean_closure_set(v___f_2929_, 0, v_stats_2923_);
lean_closure_set(v___f_2929_, 1, v_indTypes_2924_);
lean_closure_set(v___f_2929_, 2, v___x_2928_);
lean_closure_set(v___f_2929_, 3, v_k_2926_);
v___x_2930_ = ((lean_object*)(l_Lean4Lean_AddInductive_mkRecInfos___redArg___closed__0));
v___x_2931_ = l_Lean4Lean_AddInductive_mkRecInfos_loopInd1___redArg(v_stats_2923_, v_indTypes_2924_, v_elimLevel_2925_, v___x_2928_, v___x_2930_, v___f_2929_, v_a_2927_);
return v___x_2931_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___redArg___boxed(lean_object* v_stats_2932_, lean_object* v_indTypes_2933_, lean_object* v_elimLevel_2934_, lean_object* v_k_2935_, lean_object* v_a_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l_Lean4Lean_AddInductive_mkRecInfos___redArg(v_stats_2932_, v_indTypes_2933_, v_elimLevel_2934_, v_k_2935_, v_a_2936_);
lean_dec_ref(v_a_2936_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos(lean_object* v_00_u03b1_2938_, lean_object* v_stats_2939_, lean_object* v_indTypes_2940_, lean_object* v_elimLevel_2941_, lean_object* v_k_2942_, lean_object* v_a_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean4Lean_AddInductive_mkRecInfos___redArg(v_stats_2939_, v_indTypes_2940_, v_elimLevel_2941_, v_k_2942_, v_a_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecInfos___boxed(lean_object* v_00_u03b1_2945_, lean_object* v_stats_2946_, lean_object* v_indTypes_2947_, lean_object* v_elimLevel_2948_, lean_object* v_k_2949_, lean_object* v_a_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean4Lean_AddInductive_mkRecInfos(v_00_u03b1_2945_, v_stats_2946_, v_indTypes_2947_, v_elimLevel_2948_, v_k_2949_, v_a_2950_);
lean_dec_ref(v_a_2950_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getRecLevels(lean_object* v_elimLevel_2952_, lean_object* v_levels_2953_){
_start:
{
uint8_t v___x_2954_; 
v___x_2954_ = l_Lean_Level_isParam(v_elimLevel_2952_);
if (v___x_2954_ == 0)
{
lean_dec(v_elimLevel_2952_);
return v_levels_2953_;
}
else
{
lean_object* v___x_2955_; 
v___x_2955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2955_, 0, v_elimLevel_2952_);
lean_ctor_set(v___x_2955_, 1, v_levels_2953_);
return v___x_2955_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getRecLevelParams(lean_object* v_elimLevel_2956_, lean_object* v_lparams_2957_){
_start:
{
if (lean_obj_tag(v_elimLevel_2956_) == 4)
{
lean_object* v_a_2958_; lean_object* v___x_2959_; 
v_a_2958_ = lean_ctor_get(v_elimLevel_2956_, 0);
lean_inc(v_a_2958_);
v___x_2959_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2959_, 0, v_a_2958_);
lean_ctor_set(v___x_2959_, 1, v_lparams_2957_);
return v___x_2959_;
}
else
{
return v_lparams_2957_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_getRecLevelParams___boxed(lean_object* v_elimLevel_2960_, lean_object* v_lparams_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean4Lean_AddInductive_getRecLevelParams(v_elimLevel_2960_, v_lparams_2961_);
lean_dec(v_elimLevel_2960_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU___lam__0(lean_object* v_stats_2963_, lean_object* v_indTypes_2964_, lean_object* v_lvls_2965_, lean_object* v_motives_2966_, lean_object* v_minors_2967_, lean_object* v_ui_2968_, uint8_t v___x_2969_, lean_object* v_uiTy_2970_, lean_object* v_xs_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v___y_2974_; lean_object* v___x_3001_; 
lean_inc_ref(v_uiTy_2970_);
lean_inc_ref(v_stats_2963_);
v___x_3001_ = l_Lean4Lean_AddInductive_isValidIndApp_x3f(v_stats_2963_, v_uiTy_2970_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v___x_3002_; lean_object* v___x_3003_; 
v___x_3002_ = lean_obj_once(&l_Lean4Lean_AddInductive_getIIndices___closed__3, &l_Lean4Lean_AddInductive_getIIndices___closed__3_once, _init_l_Lean4Lean_AddInductive_getIIndices___closed__3);
v___x_3003_ = l_panic___at___00Lean4Lean_AddInductive_declareConstructors_spec__0(v___x_3002_);
v___y_2974_ = v___x_3003_;
goto v___jp_2973_;
}
else
{
lean_object* v_val_3004_; 
v_val_3004_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_val_3004_);
lean_dec_ref(v___x_3001_);
v___y_2974_ = v_val_3004_;
goto v___jp_2973_;
}
v___jp_2973_:
{
lean_object* v_params_2975_; lean_object* v_nargs_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v_name_2979_; lean_object* v_lctx_2980_; lean_object* v_dummy_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; lean_object* v_a_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_val_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_val_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; uint8_t v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; 
v_params_2975_ = lean_ctor_get(v_stats_2963_, 5);
lean_inc_ref(v_params_2975_);
lean_dec_ref(v_stats_2963_);
v_nargs_2976_ = l_Lean_Expr_getAppNumArgs(v_uiTy_2970_);
v___x_2977_ = l_Lean_instInhabitedInductiveType_default;
v___x_2978_ = lean_array_get_borrowed(v___x_2977_, v_indTypes_2964_, v___y_2974_);
lean_dec(v___y_2974_);
v_name_2979_ = lean_ctor_get(v___x_2978_, 0);
v_lctx_2980_ = lean_ctor_get(v___y_2972_, 1);
v_dummy_2981_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
lean_inc(v_nargs_2976_);
v___x_2982_ = lean_mk_array(v_nargs_2976_, v_dummy_2981_);
v___x_2983_ = lean_unsigned_to_nat(1u);
v___x_2984_ = lean_nat_sub(v_nargs_2976_, v___x_2983_);
lean_dec(v_nargs_2976_);
v_a_2985_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_uiTy_2970_, v___x_2982_, v___x_2984_);
v___x_2986_ = lean_array_get_size(v_a_2985_);
v___x_2987_ = lean_array_get_size(v_params_2975_);
v___x_2988_ = l_Array_toSubarray___redArg(v_a_2985_, v___x_2987_, v___x_2986_);
v___x_2989_ = l_Subarray_copy___redArg(v___x_2988_);
lean_inc(v_name_2979_);
v___x_2990_ = l_Lean_mkRecName(v_name_2979_);
v_val_2991_ = l_Lean_Expr_const___override(v___x_2990_, v_lvls_2965_);
v___x_2992_ = l_Lean_mkAppN(v_val_2991_, v_params_2975_);
lean_dec_ref(v_params_2975_);
v___x_2993_ = l_Lean_mkAppN(v___x_2992_, v_motives_2966_);
v___x_2994_ = l_Lean_mkAppN(v___x_2993_, v_minors_2967_);
v_val_2995_ = l_Lean_mkAppN(v___x_2994_, v___x_2989_);
lean_dec_ref(v___x_2989_);
v___x_2996_ = l_Lean_mkAppN(v_ui_2968_, v_xs_2971_);
v___x_2997_ = l_Lean_Expr_app___override(v_val_2995_, v___x_2996_);
v___x_2998_ = 0;
lean_inc_ref(v_lctx_2980_);
v___x_2999_ = l_Lean_LocalContext_mkLambda(v_lctx_2980_, v_xs_2971_, v___x_2997_, v___x_2969_, v___x_2998_);
lean_dec_ref(v___x_2997_);
v___x_3000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3000_, 0, v___x_2999_);
return v___x_3000_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU___lam__0___boxed(lean_object* v_stats_3005_, lean_object* v_indTypes_3006_, lean_object* v_lvls_3007_, lean_object* v_motives_3008_, lean_object* v_minors_3009_, lean_object* v_ui_3010_, lean_object* v___x_3011_, lean_object* v_uiTy_3012_, lean_object* v_xs_3013_, lean_object* v___y_3014_){
_start:
{
uint8_t v___x_630__boxed_3015_; lean_object* v_res_3016_; 
v___x_630__boxed_3015_ = lean_unbox(v___x_3011_);
v_res_3016_ = l_Lean4Lean_AddInductive_mkRecRules_loopU___lam__0(v_stats_3005_, v_indTypes_3006_, v_lvls_3007_, v_motives_3008_, v_minors_3009_, v_ui_3010_, v___x_630__boxed_3015_, v_uiTy_3012_, v_xs_3013_, v___y_3014_);
lean_dec_ref(v___y_3014_);
lean_dec_ref(v_xs_3013_);
lean_dec_ref(v_minors_3009_);
lean_dec_ref(v_motives_3008_);
lean_dec_ref(v_indTypes_3006_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU(lean_object* v_indTypes_3017_, lean_object* v_stats_3018_, lean_object* v_motives_3019_, lean_object* v_minors_3020_, lean_object* v_lvls_3021_, lean_object* v_u_3022_, lean_object* v_i_3023_, lean_object* v_v_3024_, lean_object* v_k_3025_, lean_object* v_a_3026_){
_start:
{
lean_object* v___x_3027_; uint8_t v___x_3028_; 
v___x_3027_ = lean_array_get_size(v_u_3022_);
v___x_3028_ = lean_nat_dec_lt(v_i_3023_, v___x_3027_);
if (v___x_3028_ == 0)
{
lean_object* v___x_3029_; 
lean_dec(v_i_3023_);
lean_dec(v_lvls_3021_);
lean_dec_ref(v_minors_3020_);
lean_dec_ref(v_motives_3019_);
lean_dec_ref(v_stats_3018_);
lean_dec_ref(v_indTypes_3017_);
lean_inc_ref(v_a_3026_);
v___x_3029_ = lean_apply_2(v_k_3025_, v_v_3024_, v_a_3026_);
return v___x_3029_;
}
else
{
lean_object* v_ui_3030_; lean_object* v___x_3031_; lean_object* v___f_3032_; lean_object* v___x_3033_; 
v_ui_3030_ = lean_array_fget_borrowed(v_u_3022_, v_i_3023_);
v___x_3031_ = lean_box(v___x_3028_);
lean_inc_n(v_ui_3030_, 2);
lean_inc_ref(v_minors_3020_);
lean_inc_ref(v_motives_3019_);
lean_inc(v_lvls_3021_);
lean_inc_ref(v_indTypes_3017_);
lean_inc_ref(v_stats_3018_);
v___f_3032_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_mkRecRules_loopU___lam__0___boxed), 10, 7);
lean_closure_set(v___f_3032_, 0, v_stats_3018_);
lean_closure_set(v___f_3032_, 1, v_indTypes_3017_);
lean_closure_set(v___f_3032_, 2, v_lvls_3021_);
lean_closure_set(v___f_3032_, 3, v_motives_3019_);
lean_closure_set(v___f_3032_, 4, v_minors_3020_);
lean_closure_set(v___f_3032_, 5, v_ui_3030_);
lean_closure_set(v___f_3032_, 6, v___x_3031_);
v___x_3033_ = l_Lean4Lean_AddInductive_mkRecInfos_loopUArgs___redArg(v_ui_3030_, v___f_3032_, v_a_3026_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref(v_k_3025_);
lean_dec_ref(v_v_3024_);
lean_dec(v_i_3023_);
lean_dec(v_lvls_3021_);
lean_dec_ref(v_minors_3020_);
lean_dec_ref(v_motives_3019_);
lean_dec_ref(v_stats_3018_);
lean_dec_ref(v_indTypes_3017_);
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_3033_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; 
v_a_3042_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3042_);
lean_dec_ref(v___x_3033_);
v___x_3043_ = lean_unsigned_to_nat(1u);
v___x_3044_ = lean_nat_add(v_i_3023_, v___x_3043_);
lean_dec(v_i_3023_);
v___x_3045_ = lean_array_push(v_v_3024_, v_a_3042_);
v_i_3023_ = v___x_3044_;
v_v_3024_ = v___x_3045_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules_loopU___boxed(lean_object* v_indTypes_3047_, lean_object* v_stats_3048_, lean_object* v_motives_3049_, lean_object* v_minors_3050_, lean_object* v_lvls_3051_, lean_object* v_u_3052_, lean_object* v_i_3053_, lean_object* v_v_3054_, lean_object* v_k_3055_, lean_object* v_a_3056_){
_start:
{
lean_object* v_res_3057_; 
v_res_3057_ = l_Lean4Lean_AddInductive_mkRecRules_loopU(v_indTypes_3047_, v_stats_3048_, v_motives_3049_, v_minors_3050_, v_lvls_3051_, v_u_3052_, v_i_3053_, v_v_3054_, v_k_3055_, v_a_3056_);
lean_dec_ref(v_a_3056_);
lean_dec_ref(v_u_3052_);
return v_res_3057_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__0(lean_object* v_stats_3058_, lean_object* v_bu_3059_, lean_object* v___x_3060_, lean_object* v_minors_3061_, lean_object* v___y_3062_, lean_object* v_motives_3063_, lean_object* v_name_3064_, lean_object* v_v_3065_, lean_object* v___y_3066_){
_start:
{
lean_object* v_lctx_3067_; lean_object* v_params_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; uint8_t v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_lctx_3067_ = lean_ctor_get(v___y_3066_, 1);
v_params_3068_ = lean_ctor_get(v_stats_3058_, 5);
v___x_3069_ = lean_array_get_size(v_bu_3059_);
v___x_3070_ = lean_array_get_borrowed(v___x_3060_, v_minors_3061_, v___y_3062_);
lean_inc(v___x_3070_);
v___x_3071_ = l_Lean_mkAppN(v___x_3070_, v_bu_3059_);
v___x_3072_ = l_Lean_mkAppN(v___x_3071_, v_v_3065_);
v___x_3073_ = 1;
v___x_3074_ = 0;
lean_inc_ref_n(v_lctx_3067_, 4);
v___x_3075_ = l_Lean_LocalContext_mkLambda(v_lctx_3067_, v_bu_3059_, v___x_3072_, v___x_3073_, v___x_3074_);
lean_dec_ref(v___x_3072_);
v___x_3076_ = l_Lean_LocalContext_mkLambda(v_lctx_3067_, v_minors_3061_, v___x_3075_, v___x_3073_, v___x_3074_);
lean_dec_ref(v___x_3075_);
v___x_3077_ = l_Lean_LocalContext_mkLambda(v_lctx_3067_, v_motives_3063_, v___x_3076_, v___x_3073_, v___x_3074_);
lean_dec_ref(v___x_3076_);
v___x_3078_ = l_Lean_LocalContext_mkLambda(v_lctx_3067_, v_params_3068_, v___x_3077_, v___x_3073_, v___x_3074_);
lean_dec_ref(v___x_3077_);
v___x_3079_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3079_, 0, v_name_3064_);
lean_ctor_set(v___x_3079_, 1, v___x_3069_);
lean_ctor_set(v___x_3079_, 2, v___x_3078_);
v___x_3080_ = lean_unsigned_to_nat(1u);
v___x_3081_ = lean_nat_add(v___y_3062_, v___x_3080_);
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3079_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
v___x_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
return v___x_3083_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__0___boxed(lean_object* v_stats_3084_, lean_object* v_bu_3085_, lean_object* v___x_3086_, lean_object* v_minors_3087_, lean_object* v___y_3088_, lean_object* v_motives_3089_, lean_object* v_name_3090_, lean_object* v_v_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v_res_3093_; 
v_res_3093_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__0(v_stats_3084_, v_bu_3085_, v___x_3086_, v_minors_3087_, v___y_3088_, v_motives_3089_, v_name_3090_, v_v_3091_, v___y_3092_);
lean_dec_ref(v___y_3092_);
lean_dec_ref(v_v_3091_);
lean_dec_ref(v_motives_3089_);
lean_dec(v___y_3088_);
lean_dec_ref(v_minors_3087_);
lean_dec_ref(v___x_3086_);
lean_dec_ref(v_bu_3085_);
lean_dec_ref(v_stats_3084_);
return v_res_3093_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__1(lean_object* v_stats_3094_, lean_object* v___x_3095_, lean_object* v_minors_3096_, lean_object* v___y_3097_, lean_object* v_motives_3098_, lean_object* v_name_3099_, lean_object* v_indTypes_3100_, lean_object* v_lvls_3101_, lean_object* v_x_3102_, lean_object* v_bu_3103_, lean_object* v_u_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___f_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_inc_ref(v_motives_3098_);
lean_inc_ref(v_minors_3096_);
lean_inc_ref(v_stats_3094_);
v___f_3106_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__0___boxed), 9, 7);
lean_closure_set(v___f_3106_, 0, v_stats_3094_);
lean_closure_set(v___f_3106_, 1, v_bu_3103_);
lean_closure_set(v___f_3106_, 2, v___x_3095_);
lean_closure_set(v___f_3106_, 3, v_minors_3096_);
lean_closure_set(v___f_3106_, 4, v___y_3097_);
lean_closure_set(v___f_3106_, 5, v_motives_3098_);
lean_closure_set(v___f_3106_, 6, v_name_3099_);
v___x_3107_ = lean_unsigned_to_nat(0u);
v___x_3108_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
v___x_3109_ = l_Lean4Lean_AddInductive_mkRecRules_loopU(v_indTypes_3100_, v_stats_3094_, v_motives_3098_, v_minors_3096_, v_lvls_3101_, v_u_3104_, v___x_3107_, v___x_3108_, v___f_3106_, v___y_3105_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__1___boxed(lean_object* v_stats_3110_, lean_object* v___x_3111_, lean_object* v_minors_3112_, lean_object* v___y_3113_, lean_object* v_motives_3114_, lean_object* v_name_3115_, lean_object* v_indTypes_3116_, lean_object* v_lvls_3117_, lean_object* v_x_3118_, lean_object* v_bu_3119_, lean_object* v_u_3120_, lean_object* v___y_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__1(v_stats_3110_, v___x_3111_, v_minors_3112_, v___y_3113_, v_motives_3114_, v_name_3115_, v_indTypes_3116_, v_lvls_3117_, v_x_3118_, v_bu_3119_, v_u_3120_, v___y_3121_);
lean_dec_ref(v___y_3121_);
lean_dec_ref(v_u_3120_);
lean_dec_ref(v_x_3118_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg(lean_object* v_stats_3123_, lean_object* v_minors_3124_, lean_object* v_motives_3125_, lean_object* v_indTypes_3126_, lean_object* v_lvls_3127_, lean_object* v_as_x27_3128_, lean_object* v_b_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
if (lean_obj_tag(v_as_x27_3128_) == 0)
{
lean_object* v___x_3132_; lean_object* v___x_3133_; 
lean_dec(v_lvls_3127_);
lean_dec_ref(v_indTypes_3126_);
lean_dec_ref(v_motives_3125_);
lean_dec_ref(v_minors_3124_);
lean_dec_ref(v_stats_3123_);
v___x_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3132_, 0, v_b_3129_);
lean_ctor_set(v___x_3132_, 1, v___y_3130_);
v___x_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3133_, 0, v___x_3132_);
return v___x_3133_;
}
else
{
lean_object* v_head_3134_; lean_object* v_tail_3135_; lean_object* v_name_3136_; lean_object* v_type_3137_; lean_object* v___x_3138_; lean_object* v___f_3139_; lean_object* v___x_3140_; 
v_head_3134_ = lean_ctor_get(v_as_x27_3128_, 0);
v_tail_3135_ = lean_ctor_get(v_as_x27_3128_, 1);
v_name_3136_ = lean_ctor_get(v_head_3134_, 0);
v_type_3137_ = lean_ctor_get(v_head_3134_, 1);
v___x_3138_ = l_Lean_instInhabitedExpr;
lean_inc(v_lvls_3127_);
lean_inc_ref(v_indTypes_3126_);
lean_inc(v_name_3136_);
lean_inc_ref(v_motives_3125_);
lean_inc_ref(v_minors_3124_);
lean_inc_ref_n(v_stats_3123_, 2);
v___f_3139_ = lean_alloc_closure((void*)(l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___lam__1___boxed), 12, 8);
lean_closure_set(v___f_3139_, 0, v_stats_3123_);
lean_closure_set(v___f_3139_, 1, v___x_3138_);
lean_closure_set(v___f_3139_, 2, v_minors_3124_);
lean_closure_set(v___f_3139_, 3, v___y_3130_);
lean_closure_set(v___f_3139_, 4, v_motives_3125_);
lean_closure_set(v___f_3139_, 5, v_name_3136_);
lean_closure_set(v___f_3139_, 6, v_indTypes_3126_);
lean_closure_set(v___f_3139_, 7, v_lvls_3127_);
lean_inc_ref(v_type_3137_);
v___x_3140_ = l_Lean4Lean_AddInductive_mkRecInfos_loopCtorArgs___redArg(v_stats_3123_, v_type_3137_, v___f_3139_, v___y_3131_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
lean_dec_ref(v_b_3129_);
lean_dec(v_lvls_3127_);
lean_dec_ref(v_indTypes_3126_);
lean_dec_ref(v_motives_3125_);
lean_dec_ref(v_minors_3124_);
lean_dec_ref(v_stats_3123_);
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v_fst_3150_; lean_object* v_snd_3151_; lean_object* v___x_3152_; 
v_a_3149_ = lean_ctor_get(v___x_3140_, 0);
lean_inc(v_a_3149_);
lean_dec_ref(v___x_3140_);
v_fst_3150_ = lean_ctor_get(v_a_3149_, 0);
lean_inc(v_fst_3150_);
v_snd_3151_ = lean_ctor_get(v_a_3149_, 1);
lean_inc(v_snd_3151_);
lean_dec(v_a_3149_);
v___x_3152_ = lean_array_push(v_b_3129_, v_fst_3150_);
v_as_x27_3128_ = v_tail_3135_;
v_b_3129_ = v___x_3152_;
v___y_3130_ = v_snd_3151_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg___boxed(lean_object* v_stats_3154_, lean_object* v_minors_3155_, lean_object* v_motives_3156_, lean_object* v_indTypes_3157_, lean_object* v_lvls_3158_, lean_object* v_as_x27_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_){
_start:
{
lean_object* v_res_3163_; 
v_res_3163_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg(v_stats_3154_, v_minors_3155_, v_motives_3156_, v_indTypes_3157_, v_lvls_3158_, v_as_x27_3159_, v_b_3160_, v___y_3161_, v___y_3162_);
lean_dec_ref(v___y_3162_);
lean_dec(v_as_x27_3159_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules(lean_object* v_indTypes_3166_, lean_object* v_elimLevel_3167_, lean_object* v_stats_3168_, lean_object* v_dIdx_3169_, lean_object* v_motives_3170_, lean_object* v_minors_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_){
_start:
{
lean_object* v_levels_3174_; lean_object* v___x_3175_; lean_object* v_d_3176_; lean_object* v_ctors_3177_; lean_object* v_lvls_3178_; lean_object* v_rules_3179_; lean_object* v___x_3180_; 
v_levels_3174_ = lean_ctor_get(v_stats_3168_, 1);
v___x_3175_ = l_Lean_instInhabitedInductiveType_default;
v_d_3176_ = lean_array_get_borrowed(v___x_3175_, v_indTypes_3166_, v_dIdx_3169_);
v_ctors_3177_ = lean_ctor_get(v_d_3176_, 2);
lean_inc(v_ctors_3177_);
lean_inc(v_levels_3174_);
v_lvls_3178_ = l_Lean4Lean_AddInductive_getRecLevels(v_elimLevel_3167_, v_levels_3174_);
v_rules_3179_ = ((lean_object*)(l_Lean4Lean_AddInductive_mkRecRules___closed__0));
v___x_3180_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg(v_stats_3168_, v_minors_3171_, v_motives_3170_, v_indTypes_3166_, v_lvls_3178_, v_ctors_3177_, v_rules_3179_, v_a_3172_, v_a_3173_);
lean_dec(v_ctors_3177_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3180_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_dec(v___x_3180_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3206_; 
v_a_3189_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3206_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3206_ == 0)
{
v___x_3191_ = v___x_3180_;
v_isShared_3192_ = v_isSharedCheck_3206_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_a_3189_);
lean_dec(v___x_3180_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3206_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v_fst_3193_; lean_object* v_snd_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3205_; 
v_fst_3193_ = lean_ctor_get(v_a_3189_, 0);
v_snd_3194_ = lean_ctor_get(v_a_3189_, 1);
v_isSharedCheck_3205_ = !lean_is_exclusive(v_a_3189_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3196_ = v_a_3189_;
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_snd_3194_);
lean_inc(v_fst_3193_);
lean_dec(v_a_3189_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3205_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3198_; lean_object* v___x_3200_; 
v___x_3198_ = lean_array_to_list(v_fst_3193_);
if (v_isShared_3197_ == 0)
{
lean_ctor_set(v___x_3196_, 0, v___x_3198_);
v___x_3200_ = v___x_3196_;
goto v_reusejp_3199_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v___x_3198_);
lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_snd_3194_);
v___x_3200_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3199_;
}
v_reusejp_3199_:
{
lean_object* v___x_3202_; 
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 0, v___x_3200_);
v___x_3202_ = v___x_3191_;
goto v_reusejp_3201_;
}
else
{
lean_object* v_reuseFailAlloc_3203_; 
v_reuseFailAlloc_3203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
v___x_3202_ = v_reuseFailAlloc_3203_;
goto v_reusejp_3201_;
}
v_reusejp_3201_:
{
return v___x_3202_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_mkRecRules___boxed(lean_object* v_indTypes_3207_, lean_object* v_elimLevel_3208_, lean_object* v_stats_3209_, lean_object* v_dIdx_3210_, lean_object* v_motives_3211_, lean_object* v_minors_3212_, lean_object* v_a_3213_, lean_object* v_a_3214_){
_start:
{
lean_object* v_res_3215_; 
v_res_3215_ = l_Lean4Lean_AddInductive_mkRecRules(v_indTypes_3207_, v_elimLevel_3208_, v_stats_3209_, v_dIdx_3210_, v_motives_3211_, v_minors_3212_, v_a_3213_, v_a_3214_);
lean_dec_ref(v_a_3214_);
lean_dec(v_dIdx_3210_);
return v_res_3215_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0(lean_object* v_stats_3216_, lean_object* v_minors_3217_, lean_object* v_motives_3218_, lean_object* v_indTypes_3219_, lean_object* v_lvls_3220_, lean_object* v_as_3221_, lean_object* v_as_x27_3222_, lean_object* v_b_3223_, lean_object* v_a_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___x_3227_; 
v___x_3227_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___redArg(v_stats_3216_, v_minors_3217_, v_motives_3218_, v_indTypes_3219_, v_lvls_3220_, v_as_x27_3222_, v_b_3223_, v___y_3225_, v___y_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0___boxed(lean_object* v_stats_3228_, lean_object* v_minors_3229_, lean_object* v_motives_3230_, lean_object* v_indTypes_3231_, lean_object* v_lvls_3232_, lean_object* v_as_3233_, lean_object* v_as_x27_3234_, lean_object* v_b_3235_, lean_object* v_a_3236_, lean_object* v___y_3237_, lean_object* v___y_3238_){
_start:
{
lean_object* v_res_3239_; 
v_res_3239_ = l_List_forIn_x27_loop___at___00Lean4Lean_AddInductive_mkRecRules_spec__0(v_stats_3228_, v_minors_3229_, v_motives_3230_, v_indTypes_3231_, v_lvls_3232_, v_as_3233_, v_as_x27_3234_, v_b_3235_, v_a_3236_, v___y_3237_, v___y_3238_);
lean_dec_ref(v___y_3238_);
lean_dec(v_as_x27_3234_);
lean_dec(v_as_3233_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_run_spec__0(size_t v_sz_3240_, size_t v_i_3241_, lean_object* v_bs_3242_){
_start:
{
uint8_t v___x_3243_; 
v___x_3243_ = lean_usize_dec_lt(v_i_3241_, v_sz_3240_);
if (v___x_3243_ == 0)
{
return v_bs_3242_;
}
else
{
lean_object* v_v_3244_; lean_object* v_motive_3245_; lean_object* v___x_3246_; lean_object* v_bs_x27_3247_; size_t v___x_3248_; size_t v___x_3249_; lean_object* v___x_3250_; 
v_v_3244_ = lean_array_uget_borrowed(v_bs_3242_, v_i_3241_);
v_motive_3245_ = lean_ctor_get(v_v_3244_, 0);
lean_inc_ref(v_motive_3245_);
v___x_3246_ = lean_unsigned_to_nat(0u);
v_bs_x27_3247_ = lean_array_uset(v_bs_3242_, v_i_3241_, v___x_3246_);
v___x_3248_ = ((size_t)1ULL);
v___x_3249_ = lean_usize_add(v_i_3241_, v___x_3248_);
v___x_3250_ = lean_array_uset(v_bs_x27_3247_, v_i_3241_, v_motive_3245_);
v_i_3241_ = v___x_3249_;
v_bs_3242_ = v___x_3250_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_run_spec__0___boxed(lean_object* v_sz_3252_, lean_object* v_i_3253_, lean_object* v_bs_3254_){
_start:
{
size_t v_sz_boxed_3255_; size_t v_i_boxed_3256_; lean_object* v_res_3257_; 
v_sz_boxed_3255_ = lean_unbox_usize(v_sz_3252_);
lean_dec(v_sz_3252_);
v_i_boxed_3256_ = lean_unbox_usize(v_i_3253_);
lean_dec(v_i_3253_);
v_res_3257_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_run_spec__0(v_sz_boxed_3255_, v_i_boxed_3256_, v_bs_3254_);
return v_res_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___redArg(lean_object* v___x_3258_, lean_object* v_recInfos_3259_, lean_object* v_stats_3260_, lean_object* v___x_3261_, lean_object* v___y_3262_, lean_object* v___x_3263_, lean_object* v_a_3264_, uint8_t v_allowPrimitive_3265_, lean_object* v_lparams_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, lean_object* v___x_3269_, uint8_t v_a_3270_, uint8_t v___y_3271_, lean_object* v_range_3272_, lean_object* v_b_3273_, lean_object* v_i_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_stop_3277_; lean_object* v_step_3278_; uint8_t v___x_3279_; 
v_stop_3277_ = lean_ctor_get(v_range_3272_, 1);
v_step_3278_ = lean_ctor_get(v_range_3272_, 2);
v___x_3279_ = lean_nat_dec_lt(v_i_3274_, v_stop_3277_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec(v_i_3274_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
lean_dec(v___x_3267_);
lean_dec(v_lparams_3266_);
lean_dec(v_a_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___x_3261_);
lean_dec_ref(v_stats_3260_);
lean_dec_ref(v___x_3258_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v_b_3273_);
lean_ctor_set(v___x_3280_, 1, v___y_3275_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
return v___x_3281_;
}
else
{
lean_object* v_nindices_3282_; lean_object* v_params_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v_motive_3286_; lean_object* v_indices_3287_; lean_object* v_major_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_nindices_3282_ = lean_ctor_get(v_stats_3260_, 3);
v_params_3283_ = lean_ctor_get(v_stats_3260_, 5);
v___x_3284_ = l_Lean4Lean_AddInductive_instInhabitedRecInfo_default;
v___x_3285_ = lean_array_get_borrowed(v___x_3284_, v_recInfos_3259_, v_i_3274_);
v_motive_3286_ = lean_ctor_get(v___x_3285_, 0);
v_indices_3287_ = lean_ctor_get(v___x_3285_, 2);
v_major_3288_ = lean_ctor_get(v___x_3285_, 3);
v___x_3289_ = lean_array_fget(v___x_3258_, v_i_3274_);
v___x_3290_ = lean_unsigned_to_nat(1u);
v___x_3291_ = lean_mk_empty_array_with_capacity(v___x_3290_);
lean_inc_ref_n(v_major_3288_, 2);
v___x_3292_ = lean_array_push(v___x_3291_, v_major_3288_);
lean_inc_ref(v_motive_3286_);
v___x_3293_ = l_Lean_mkAppN(v_motive_3286_, v_indices_3287_);
v___x_3294_ = l_Lean_Expr_app___override(v___x_3293_, v_major_3288_);
v___x_3295_ = 0;
lean_inc_ref_n(v___x_3261_, 4);
v___x_3296_ = l_Lean_LocalContext_mkForall(v___x_3261_, v___x_3292_, v___x_3294_, v___x_3279_, v___x_3295_);
lean_dec_ref(v___x_3294_);
lean_dec_ref(v___x_3292_);
v___x_3297_ = l_Lean_LocalContext_mkForall(v___x_3261_, v_indices_3287_, v___x_3296_, v___x_3279_, v___x_3295_);
lean_dec_ref(v___x_3296_);
v___x_3298_ = l_Lean_LocalContext_mkForall(v___x_3261_, v___y_3262_, v___x_3297_, v___x_3279_, v___x_3295_);
lean_dec_ref(v___x_3297_);
v___x_3299_ = l_Lean_LocalContext_mkForall(v___x_3261_, v___x_3263_, v___x_3298_, v___x_3279_, v___x_3295_);
lean_dec_ref(v___x_3298_);
lean_inc_ref(v___y_3262_);
lean_inc_ref(v___x_3263_);
lean_inc_ref(v_stats_3260_);
lean_inc(v_a_3264_);
lean_inc_ref(v___x_3258_);
v___x_3300_ = l_Lean4Lean_AddInductive_mkRecRules(v___x_3258_, v_a_3264_, v_stats_3260_, v_i_3274_, v___x_3263_, v___y_3262_, v___y_3275_, v___y_3276_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v___x_3299_);
lean_dec(v___x_3289_);
lean_dec(v_i_3274_);
lean_dec_ref(v_b_3273_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
lean_dec(v___x_3267_);
lean_dec(v_lparams_3266_);
lean_dec(v_a_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___x_3261_);
lean_dec_ref(v_stats_3260_);
lean_dec_ref(v___x_3258_);
v_a_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v_fst_3310_; lean_object* v_snd_3311_; lean_object* v_name_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3341_; 
v_a_3309_ = lean_ctor_get(v___x_3300_, 0);
lean_inc(v_a_3309_);
lean_dec_ref(v___x_3300_);
v_fst_3310_ = lean_ctor_get(v_a_3309_, 0);
lean_inc(v_fst_3310_);
v_snd_3311_ = lean_ctor_get(v_a_3309_, 1);
lean_inc(v_snd_3311_);
lean_dec(v_a_3309_);
v_name_3312_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; lean_object* v_unused_3343_; 
v_unused_3342_ = lean_ctor_get(v___x_3289_, 2);
lean_dec(v_unused_3342_);
v_unused_3343_ = lean_ctor_get(v___x_3289_, 1);
lean_dec(v_unused_3343_);
v___x_3314_ = v___x_3289_;
v_isShared_3315_ = v_isSharedCheck_3341_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_name_3312_);
lean_dec(v___x_3289_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3341_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3316_; lean_object* v___x_3317_; 
v___x_3316_ = l_Lean_mkRecName(v_name_3312_);
lean_inc(v___x_3316_);
lean_inc_ref(v_b_3273_);
v___x_3317_ = l_Lean_Kernel_Environment_checkName(v_b_3273_, v___x_3316_, v_allowPrimitive_3265_);
if (lean_obj_tag(v___x_3317_) == 0)
{
lean_object* v_a_3318_; lean_object* v___x_3320_; uint8_t v_isShared_3321_; uint8_t v_isSharedCheck_3325_; 
lean_dec(v___x_3316_);
lean_del_object(v___x_3314_);
lean_dec(v_snd_3311_);
lean_dec(v_fst_3310_);
lean_dec_ref(v___x_3299_);
lean_dec(v_i_3274_);
lean_dec_ref(v_b_3273_);
lean_dec(v___x_3269_);
lean_dec(v___x_3268_);
lean_dec(v___x_3267_);
lean_dec(v_lparams_3266_);
lean_dec(v_a_3264_);
lean_dec_ref(v___x_3263_);
lean_dec_ref(v___y_3262_);
lean_dec_ref(v___x_3261_);
lean_dec_ref(v_stats_3260_);
lean_dec_ref(v___x_3258_);
v_a_3318_ = lean_ctor_get(v___x_3317_, 0);
v_isSharedCheck_3325_ = !lean_is_exclusive(v___x_3317_);
if (v_isSharedCheck_3325_ == 0)
{
v___x_3320_ = v___x_3317_;
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
else
{
lean_inc(v_a_3318_);
lean_dec(v___x_3317_);
v___x_3320_ = lean_box(0);
v_isShared_3321_ = v_isSharedCheck_3325_;
goto v_resetjp_3319_;
}
v_resetjp_3319_:
{
lean_object* v___x_3323_; 
if (v_isShared_3321_ == 0)
{
v___x_3323_ = v___x_3320_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_a_3318_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
return v___x_3323_;
}
}
}
else
{
lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3332_; 
lean_dec_ref(v___x_3317_);
v___x_3326_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v___x_3261_);
v___x_3327_ = l_Lean_LocalContext_mkForall(v___x_3261_, v_params_3283_, v___x_3299_, v___x_3279_, v___x_3295_);
lean_dec_ref(v___x_3299_);
lean_inc(v_lparams_3266_);
v___x_3328_ = l_Lean4Lean_AddInductive_getRecLevelParams(v_a_3264_, v_lparams_3266_);
v___x_3329_ = lean_unsigned_to_nat(1000u);
v___x_3330_ = l_Lean_Expr_inferImplicit(v___x_3327_, v___x_3329_, v___x_3295_);
if (v_isShared_3315_ == 0)
{
lean_ctor_set(v___x_3314_, 2, v___x_3330_);
lean_ctor_set(v___x_3314_, 1, v___x_3328_);
lean_ctor_set(v___x_3314_, 0, v___x_3316_);
v___x_3332_ = v___x_3314_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v___x_3328_);
lean_ctor_set(v_reuseFailAlloc_3340_, 2, v___x_3330_);
v___x_3332_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3333_ = lean_array_get_size(v_params_3283_);
v___x_3334_ = lean_array_get_borrowed(v___x_3326_, v_nindices_3282_, v_i_3274_);
lean_inc(v___x_3269_);
lean_inc(v___x_3268_);
lean_inc(v___x_3334_);
lean_inc(v___x_3267_);
v___x_3335_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_3335_, 0, v___x_3332_);
lean_ctor_set(v___x_3335_, 1, v___x_3267_);
lean_ctor_set(v___x_3335_, 2, v___x_3333_);
lean_ctor_set(v___x_3335_, 3, v___x_3334_);
lean_ctor_set(v___x_3335_, 4, v___x_3268_);
lean_ctor_set(v___x_3335_, 5, v___x_3269_);
lean_ctor_set(v___x_3335_, 6, v_fst_3310_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7, v_a_3270_);
lean_ctor_set_uint8(v___x_3335_, sizeof(void*)*7 + 1, v___y_3271_);
v___x_3336_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v___x_3336_, 0, v___x_3335_);
v___x_3337_ = lean_environment_add(v_b_3273_, v___x_3336_);
v___x_3338_ = lean_nat_add(v_i_3274_, v_step_3278_);
lean_dec(v_i_3274_);
v_b_3273_ = v___x_3337_;
v_i_3274_ = v___x_3338_;
v___y_3275_ = v_snd_3311_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___redArg___boxed(lean_object** _args){
lean_object* v___x_3344_ = _args[0];
lean_object* v_recInfos_3345_ = _args[1];
lean_object* v_stats_3346_ = _args[2];
lean_object* v___x_3347_ = _args[3];
lean_object* v___y_3348_ = _args[4];
lean_object* v___x_3349_ = _args[5];
lean_object* v_a_3350_ = _args[6];
lean_object* v_allowPrimitive_3351_ = _args[7];
lean_object* v_lparams_3352_ = _args[8];
lean_object* v___x_3353_ = _args[9];
lean_object* v___x_3354_ = _args[10];
lean_object* v___x_3355_ = _args[11];
lean_object* v_a_3356_ = _args[12];
lean_object* v___y_3357_ = _args[13];
lean_object* v_range_3358_ = _args[14];
lean_object* v_b_3359_ = _args[15];
lean_object* v_i_3360_ = _args[16];
lean_object* v___y_3361_ = _args[17];
lean_object* v___y_3362_ = _args[18];
_start:
{
uint8_t v_allowPrimitive_9305__boxed_3363_; uint8_t v_a_9310__boxed_3364_; uint8_t v___y_9311__boxed_3365_; lean_object* v_res_3366_; 
v_allowPrimitive_9305__boxed_3363_ = lean_unbox(v_allowPrimitive_3351_);
v_a_9310__boxed_3364_ = lean_unbox(v_a_3356_);
v___y_9311__boxed_3365_ = lean_unbox(v___y_3357_);
v_res_3366_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___redArg(v___x_3344_, v_recInfos_3345_, v_stats_3346_, v___x_3347_, v___y_3348_, v___x_3349_, v_a_3350_, v_allowPrimitive_9305__boxed_3363_, v_lparams_3352_, v___x_3353_, v___x_3354_, v___x_3355_, v_a_9310__boxed_3364_, v___y_9311__boxed_3365_, v_range_3358_, v_b_3359_, v_i_3360_, v___y_3361_, v___y_3362_);
lean_dec_ref(v___y_3362_);
lean_dec_ref(v_range_3358_);
lean_dec_ref(v_recInfos_3345_);
return v_res_3366_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_run_spec__2(lean_object* v_as_3367_, size_t v_i_3368_, size_t v_stop_3369_, lean_object* v_b_3370_){
_start:
{
uint8_t v___x_3371_; 
v___x_3371_ = lean_usize_dec_eq(v_i_3368_, v_stop_3369_);
if (v___x_3371_ == 0)
{
lean_object* v___x_3372_; lean_object* v_minors_3373_; lean_object* v___x_3374_; size_t v___x_3375_; size_t v___x_3376_; 
v___x_3372_ = lean_array_uget_borrowed(v_as_3367_, v_i_3368_);
v_minors_3373_ = lean_ctor_get(v___x_3372_, 1);
v___x_3374_ = l_Array_append___redArg(v_b_3370_, v_minors_3373_);
v___x_3375_ = ((size_t)1ULL);
v___x_3376_ = lean_usize_add(v_i_3368_, v___x_3375_);
v_i_3368_ = v___x_3376_;
v_b_3370_ = v___x_3374_;
goto _start;
}
else
{
return v_b_3370_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_run_spec__2___boxed(lean_object* v_as_3378_, lean_object* v_i_3379_, lean_object* v_stop_3380_, lean_object* v_b_3381_){
_start:
{
size_t v_i_boxed_3382_; size_t v_stop_boxed_3383_; lean_object* v_res_3384_; 
v_i_boxed_3382_ = lean_unbox_usize(v_i_3379_);
lean_dec(v_i_3379_);
v_stop_boxed_3383_ = lean_unbox_usize(v_stop_3380_);
lean_dec(v_stop_3380_);
v_res_3384_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_run_spec__2(v_as_3378_, v_i_boxed_3382_, v_stop_boxed_3383_, v_b_3381_);
lean_dec_ref(v_as_3378_);
return v_res_3384_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__0(lean_object* v___x_3385_, lean_object* v_stats_3386_, lean_object* v_a_3387_, lean_object* v_lparams_3388_, uint8_t v___x_3389_, lean_object* v_recInfos_3390_, lean_object* v___y_3391_){
_start:
{
size_t v_sz_3392_; size_t v___x_3393_; lean_object* v___x_3394_; lean_object* v___y_3396_; uint8_t v___y_3397_; lean_object* v___y_3398_; uint8_t v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; uint8_t v___y_3406_; lean_object* v___y_3433_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; 
v_sz_3392_ = lean_array_size(v_recInfos_3390_);
v___x_3393_ = ((size_t)0ULL);
lean_inc_ref(v_recInfos_3390_);
v___x_3394_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_run_spec__0(v_sz_3392_, v___x_3393_, v_recInfos_3390_);
v___x_3451_ = lean_unsigned_to_nat(0u);
v___x_3452_ = ((lean_object*)(l_Lean4Lean_AddInductive_instInhabitedRecInfo_default___closed__3));
v___x_3453_ = lean_array_get_size(v_recInfos_3390_);
v___x_3454_ = lean_nat_dec_lt(v___x_3451_, v___x_3453_);
if (v___x_3454_ == 0)
{
v___y_3433_ = v___x_3452_;
goto v___jp_3432_;
}
else
{
uint8_t v___x_3455_; 
v___x_3455_ = lean_nat_dec_le(v___x_3453_, v___x_3453_);
if (v___x_3455_ == 0)
{
if (v___x_3454_ == 0)
{
v___y_3433_ = v___x_3452_;
goto v___jp_3432_;
}
else
{
size_t v___x_3456_; lean_object* v___x_3457_; 
v___x_3456_ = lean_usize_of_nat(v___x_3453_);
v___x_3457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_run_spec__2(v_recInfos_3390_, v___x_3393_, v___x_3456_, v___x_3452_);
v___y_3433_ = v___x_3457_;
goto v___jp_3432_;
}
}
else
{
size_t v___x_3458_; lean_object* v___x_3459_; 
v___x_3458_ = lean_usize_of_nat(v___x_3453_);
v___x_3459_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_AddInductive_run_spec__2(v_recInfos_3390_, v___x_3393_, v___x_3458_, v___x_3452_);
v___y_3433_ = v___x_3459_;
goto v___jp_3432_;
}
}
v___jp_3395_:
{
lean_object* v___x_3407_; lean_object* v___x_3408_; 
v___x_3407_ = lean_alloc_closure((void*)(l_Lean_Kernel_TypeChecker_getEnv___boxed), 2, 0);
lean_inc(v___y_3404_);
lean_inc_ref(v___y_3396_);
lean_inc_ref(v___y_3405_);
v___x_3408_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v___y_3405_, v___y_3400_, v___y_3396_, v___y_3404_, v___x_3407_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec(v___y_3398_);
lean_dec_ref(v___x_3394_);
lean_dec_ref(v_recInfos_3390_);
lean_dec(v_lparams_3388_);
lean_dec(v_a_3387_);
lean_dec_ref(v_stats_3386_);
lean_dec_ref(v___x_3385_);
return v___x_3408_;
}
else
{
lean_object* v_a_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = lean_unsigned_to_nat(0u);
v___x_3411_ = lean_array_get_size(v___x_3385_);
v___x_3412_ = lean_unsigned_to_nat(1u);
v___x_3413_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3413_, 0, v___x_3410_);
lean_ctor_set(v___x_3413_, 1, v___x_3411_);
lean_ctor_set(v___x_3413_, 2, v___x_3412_);
lean_inc_ref(v___y_3396_);
v___x_3414_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___redArg(v___x_3385_, v_recInfos_3390_, v_stats_3386_, v___y_3396_, v___y_3402_, v___x_3394_, v_a_3387_, v___y_3397_, v_lparams_3388_, v___y_3403_, v___y_3398_, v___y_3401_, v___y_3399_, v___y_3406_, v___x_3413_, v_a_3409_, v___x_3410_, v___x_3410_, v___y_3391_);
lean_dec_ref(v___x_3413_);
lean_dec_ref(v_recInfos_3390_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; lean_object* v___x_3417_; uint8_t v_isShared_3418_; uint8_t v_isSharedCheck_3422_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3422_ == 0)
{
v___x_3417_ = v___x_3414_;
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
else
{
lean_inc(v_a_3415_);
lean_dec(v___x_3414_);
v___x_3417_ = lean_box(0);
v_isShared_3418_ = v_isSharedCheck_3422_;
goto v_resetjp_3416_;
}
v_resetjp_3416_:
{
lean_object* v___x_3420_; 
if (v_isShared_3418_ == 0)
{
v___x_3420_ = v___x_3417_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v_a_3415_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
else
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3431_; 
v_a_3423_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3425_ = v___x_3414_;
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v___x_3414_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3431_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v_fst_3427_; lean_object* v___x_3429_; 
v_fst_3427_ = lean_ctor_get(v_a_3423_, 0);
lean_inc(v_fst_3427_);
lean_dec(v_a_3423_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set(v___x_3425_, 0, v_fst_3427_);
v___x_3429_ = v___x_3425_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_fst_3427_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
}
v___jp_3432_:
{
lean_object* v___x_3434_; lean_object* v_a_3435_; lean_object* v_env_3436_; lean_object* v_lctx_3437_; lean_object* v_lparams_3438_; uint8_t v_safety_3439_; uint8_t v_allowPrimitive_3440_; size_t v_sz_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; uint8_t v___x_3446_; 
v___x_3434_ = l_Lean4Lean_AddInductive_isKTarget___redArg(v_stats_3386_, v___x_3385_);
v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
lean_inc(v_a_3435_);
lean_dec_ref(v___x_3434_);
v_env_3436_ = lean_ctor_get(v___y_3391_, 0);
v_lctx_3437_ = lean_ctor_get(v___y_3391_, 1);
v_lparams_3438_ = lean_ctor_get(v___y_3391_, 2);
v_safety_3439_ = lean_ctor_get_uint8(v___y_3391_, sizeof(void*)*4);
v_allowPrimitive_3440_ = lean_ctor_get_uint8(v___y_3391_, sizeof(void*)*4 + 1);
v_sz_3441_ = lean_array_size(v___x_3385_);
v___x_3442_ = lean_array_get_size(v___y_3433_);
v___x_3443_ = lean_array_get_size(v___x_3394_);
lean_inc_ref(v___x_3385_);
v___x_3444_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean4Lean_AddInductive_declareInductiveTypes_spec__0(v_sz_3441_, v___x_3393_, v___x_3385_);
v___x_3445_ = lean_array_to_list(v___x_3444_);
v___x_3446_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3439_, v___x_3389_);
if (v___x_3446_ == 0)
{
uint8_t v___x_3447_; uint8_t v___x_3448_; 
v___x_3447_ = 1;
v___x_3448_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
v___y_3396_ = v_lctx_3437_;
v___y_3397_ = v_allowPrimitive_3440_;
v___y_3398_ = v___x_3443_;
v___y_3399_ = v___x_3448_;
v___y_3400_ = v_safety_3439_;
v___y_3401_ = v___x_3442_;
v___y_3402_ = v___y_3433_;
v___y_3403_ = v___x_3445_;
v___y_3404_ = v_lparams_3438_;
v___y_3405_ = v_env_3436_;
v___y_3406_ = v___x_3447_;
goto v___jp_3395_;
}
else
{
uint8_t v___x_3449_; uint8_t v___x_3450_; 
v___x_3449_ = 0;
v___x_3450_ = lean_unbox(v_a_3435_);
lean_dec(v_a_3435_);
v___y_3396_ = v_lctx_3437_;
v___y_3397_ = v_allowPrimitive_3440_;
v___y_3398_ = v___x_3443_;
v___y_3399_ = v___x_3450_;
v___y_3400_ = v_safety_3439_;
v___y_3401_ = v___x_3442_;
v___y_3402_ = v___y_3433_;
v___y_3403_ = v___x_3445_;
v___y_3404_ = v_lparams_3438_;
v___y_3405_ = v_env_3436_;
v___y_3406_ = v___x_3449_;
goto v___jp_3395_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__0___boxed(lean_object* v___x_3460_, lean_object* v_stats_3461_, lean_object* v_a_3462_, lean_object* v_lparams_3463_, lean_object* v___x_3464_, lean_object* v_recInfos_3465_, lean_object* v___y_3466_){
_start:
{
uint8_t v___x_9477__boxed_3467_; lean_object* v_res_3468_; 
v___x_9477__boxed_3467_ = lean_unbox(v___x_3464_);
v_res_3468_ = l_Lean4Lean_AddInductive_run___lam__0(v___x_3460_, v_stats_3461_, v_a_3462_, v_lparams_3463_, v___x_9477__boxed_3467_, v_recInfos_3465_, v___y_3466_);
lean_dec_ref(v___y_3466_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__1(lean_object* v_nparams_3469_, lean_object* v___x_3470_, lean_object* v_numNested_3471_, uint8_t v___y_3472_, lean_object* v_lparams_3473_, uint8_t v___x_3474_, lean_object* v_stats_3475_, lean_object* v___y_3476_){
_start:
{
lean_object* v___x_3477_; 
lean_inc_ref(v___x_3470_);
lean_inc_ref(v_stats_3475_);
v___x_3477_ = l_Lean4Lean_AddInductive_declareInductiveTypes(v_stats_3475_, v_nparams_3469_, v___x_3470_, v_numNested_3471_, v___y_3472_, v___y_3476_);
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_dec_ref(v_stats_3475_);
lean_dec(v_lparams_3473_);
lean_dec_ref(v___x_3470_);
return v___x_3477_;
}
else
{
lean_object* v_a_3478_; lean_object* v_lctx_3479_; lean_object* v_lparams_3480_; lean_object* v_ngen_3481_; uint8_t v_safety_3482_; uint8_t v_allowPrimitive_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref(v___x_3477_);
v_lctx_3479_ = lean_ctor_get(v___y_3476_, 1);
v_lparams_3480_ = lean_ctor_get(v___y_3476_, 2);
v_ngen_3481_ = lean_ctor_get(v___y_3476_, 3);
v_safety_3482_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*4);
v_allowPrimitive_3483_ = lean_ctor_get_uint8(v___y_3476_, sizeof(void*)*4 + 1);
lean_inc_ref(v_ngen_3481_);
lean_inc(v_lparams_3480_);
lean_inc_ref(v_lctx_3479_);
v___x_3484_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3484_, 0, v_a_3478_);
lean_ctor_set(v___x_3484_, 1, v_lctx_3479_);
lean_ctor_set(v___x_3484_, 2, v_lparams_3480_);
lean_ctor_set(v___x_3484_, 3, v_ngen_3481_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*4, v_safety_3482_);
lean_ctor_set_uint8(v___x_3484_, sizeof(void*)*4 + 1, v_allowPrimitive_3483_);
lean_inc_ref(v_stats_3475_);
v___x_3485_ = l_Lean4Lean_AddInductive_checkConstructors(v___x_3470_, v_stats_3475_, v___y_3472_, v___x_3484_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v___x_3484_);
lean_dec_ref(v_stats_3475_);
lean_dec(v_lparams_3473_);
lean_dec_ref(v___x_3470_);
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3488_ = v___x_3485_;
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_a_3486_);
lean_dec(v___x_3485_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3493_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3491_; 
if (v_isShared_3489_ == 0)
{
v___x_3491_ = v___x_3488_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
}
else
{
lean_object* v___x_3494_; 
lean_dec_ref(v___x_3485_);
v___x_3494_ = l_Lean4Lean_AddInductive_declareConstructors(v_stats_3475_, v___x_3470_, v___y_3472_, v___x_3484_);
lean_dec_ref(v___x_3484_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_dec_ref(v_stats_3475_);
lean_dec(v_lparams_3473_);
lean_dec_ref(v___x_3470_);
return v___x_3494_;
}
else
{
lean_object* v_a_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref(v___x_3494_);
lean_inc_ref(v_ngen_3481_);
lean_inc(v_lparams_3480_);
lean_inc_ref(v_lctx_3479_);
v___x_3496_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_3496_, 0, v_a_3495_);
lean_ctor_set(v___x_3496_, 1, v_lctx_3479_);
lean_ctor_set(v___x_3496_, 2, v_lparams_3480_);
lean_ctor_set(v___x_3496_, 3, v_ngen_3481_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*4, v_safety_3482_);
lean_ctor_set_uint8(v___x_3496_, sizeof(void*)*4 + 1, v_allowPrimitive_3483_);
v___x_3497_ = l_Lean4Lean_AddInductive_getElimLevel(v_stats_3475_, v___x_3470_, v___x_3496_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v___x_3496_);
lean_dec_ref(v_stats_3475_);
lean_dec(v_lparams_3473_);
lean_dec_ref(v___x_3470_);
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; 
v_a_3506_ = lean_ctor_get(v___x_3497_, 0);
lean_inc_n(v_a_3506_, 2);
lean_dec_ref(v___x_3497_);
v___x_3507_ = lean_box(v___x_3474_);
lean_inc_ref(v_stats_3475_);
lean_inc_ref(v___x_3470_);
v___f_3508_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_run___lam__0___boxed), 7, 5);
lean_closure_set(v___f_3508_, 0, v___x_3470_);
lean_closure_set(v___f_3508_, 1, v_stats_3475_);
lean_closure_set(v___f_3508_, 2, v_a_3506_);
lean_closure_set(v___f_3508_, 3, v_lparams_3473_);
lean_closure_set(v___f_3508_, 4, v___x_3507_);
v___x_3509_ = l_Lean4Lean_AddInductive_mkRecInfos___redArg(v_stats_3475_, v___x_3470_, v_a_3506_, v___f_3508_, v___x_3496_);
lean_dec_ref(v___x_3496_);
return v___x_3509_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___lam__1___boxed(lean_object* v_nparams_3510_, lean_object* v___x_3511_, lean_object* v_numNested_3512_, lean_object* v___y_3513_, lean_object* v_lparams_3514_, lean_object* v___x_3515_, lean_object* v_stats_3516_, lean_object* v___y_3517_){
_start:
{
uint8_t v___y_9610__boxed_3518_; uint8_t v___x_9611__boxed_3519_; lean_object* v_res_3520_; 
v___y_9610__boxed_3518_ = lean_unbox(v___y_3513_);
v___x_9611__boxed_3519_ = lean_unbox(v___x_3515_);
v_res_3520_ = l_Lean4Lean_AddInductive_run___lam__1(v_nparams_3510_, v___x_3511_, v_numNested_3512_, v___y_9610__boxed_3518_, v_lparams_3514_, v___x_9611__boxed_3519_, v_stats_3516_, v___y_3517_);
lean_dec_ref(v___y_3517_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run(lean_object* v_nparams_3521_, lean_object* v_types_3522_, lean_object* v_numNested_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_lparams_3525_; uint8_t v_safety_3526_; uint8_t v___x_3527_; uint8_t v___y_3529_; uint8_t v___x_3544_; 
v_lparams_3525_ = lean_ctor_get(v_a_3524_, 2);
v_safety_3526_ = lean_ctor_get_uint8(v_a_3524_, sizeof(void*)*4);
v___x_3527_ = 1;
v___x_3544_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3526_, v___x_3527_);
if (v___x_3544_ == 0)
{
uint8_t v___x_3545_; 
v___x_3545_ = 1;
v___y_3529_ = v___x_3545_;
goto v___jp_3528_;
}
else
{
uint8_t v___x_3546_; 
v___x_3546_ = 0;
v___y_3529_ = v___x_3546_;
goto v___jp_3528_;
}
v___jp_3528_:
{
lean_object* v___x_3530_; 
lean_inc(v_lparams_3525_);
v___x_3530_ = l_Lean_Kernel_Environment_checkDuplicatedUnivParams(v_lparams_3525_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v_numNested_3523_);
lean_dec(v_types_3522_);
lean_dec(v_nparams_3521_);
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
else
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; lean_object* v___f_3542_; lean_object* v___x_3543_; 
lean_dec_ref(v___x_3530_);
v___x_3539_ = lean_array_mk(v_types_3522_);
v___x_3540_ = lean_box(v___y_3529_);
v___x_3541_ = lean_box(v___x_3527_);
lean_inc(v_lparams_3525_);
lean_inc_ref(v___x_3539_);
lean_inc(v_nparams_3521_);
v___f_3542_ = lean_alloc_closure((void*)(l_Lean4Lean_AddInductive_run___lam__1___boxed), 8, 6);
lean_closure_set(v___f_3542_, 0, v_nparams_3521_);
lean_closure_set(v___f_3542_, 1, v___x_3539_);
lean_closure_set(v___f_3542_, 2, v_numNested_3523_);
lean_closure_set(v___f_3542_, 3, v___x_3540_);
lean_closure_set(v___f_3542_, 4, v_lparams_3525_);
lean_closure_set(v___f_3542_, 5, v___x_3541_);
v___x_3543_ = l_Lean4Lean_AddInductive_checkInductiveTypes___redArg(v_nparams_3521_, v___x_3539_, v___f_3542_, v_a_3524_);
return v___x_3543_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_AddInductive_run___boxed(lean_object* v_nparams_3547_, lean_object* v_types_3548_, lean_object* v_numNested_3549_, lean_object* v_a_3550_){
_start:
{
lean_object* v_res_3551_; 
v_res_3551_ = l_Lean4Lean_AddInductive_run(v_nparams_3547_, v_types_3548_, v_numNested_3549_, v_a_3550_);
lean_dec_ref(v_a_3550_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1(lean_object* v___x_3552_, lean_object* v_recInfos_3553_, lean_object* v_stats_3554_, lean_object* v___x_3555_, lean_object* v___y_3556_, lean_object* v___x_3557_, lean_object* v_a_3558_, uint8_t v_allowPrimitive_3559_, lean_object* v_lparams_3560_, lean_object* v___x_3561_, lean_object* v___x_3562_, lean_object* v___x_3563_, uint8_t v_a_3564_, uint8_t v___y_3565_, lean_object* v_range_3566_, lean_object* v_b_3567_, lean_object* v_i_3568_, lean_object* v_hs_3569_, lean_object* v_hl_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
lean_object* v___x_3573_; 
v___x_3573_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___redArg(v___x_3552_, v_recInfos_3553_, v_stats_3554_, v___x_3555_, v___y_3556_, v___x_3557_, v_a_3558_, v_allowPrimitive_3559_, v_lparams_3560_, v___x_3561_, v___x_3562_, v___x_3563_, v_a_3564_, v___y_3565_, v_range_3566_, v_b_3567_, v_i_3568_, v___y_3571_, v___y_3572_);
return v___x_3573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1___boxed(lean_object** _args){
lean_object* v___x_3574_ = _args[0];
lean_object* v_recInfos_3575_ = _args[1];
lean_object* v_stats_3576_ = _args[2];
lean_object* v___x_3577_ = _args[3];
lean_object* v___y_3578_ = _args[4];
lean_object* v___x_3579_ = _args[5];
lean_object* v_a_3580_ = _args[6];
lean_object* v_allowPrimitive_3581_ = _args[7];
lean_object* v_lparams_3582_ = _args[8];
lean_object* v___x_3583_ = _args[9];
lean_object* v___x_3584_ = _args[10];
lean_object* v___x_3585_ = _args[11];
lean_object* v_a_3586_ = _args[12];
lean_object* v___y_3587_ = _args[13];
lean_object* v_range_3588_ = _args[14];
lean_object* v_b_3589_ = _args[15];
lean_object* v_i_3590_ = _args[16];
lean_object* v_hs_3591_ = _args[17];
lean_object* v_hl_3592_ = _args[18];
lean_object* v___y_3593_ = _args[19];
lean_object* v___y_3594_ = _args[20];
_start:
{
uint8_t v_allowPrimitive_9726__boxed_3595_; uint8_t v_a_9731__boxed_3596_; uint8_t v___y_9732__boxed_3597_; lean_object* v_res_3598_; 
v_allowPrimitive_9726__boxed_3595_ = lean_unbox(v_allowPrimitive_3581_);
v_a_9731__boxed_3596_ = lean_unbox(v_a_3586_);
v___y_9732__boxed_3597_ = lean_unbox(v___y_3587_);
v_res_3598_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_AddInductive_run_spec__1(v___x_3574_, v_recInfos_3575_, v_stats_3576_, v___x_3577_, v___y_3578_, v___x_3579_, v_a_3580_, v_allowPrimitive_9726__boxed_3595_, v_lparams_3582_, v___x_3583_, v___x_3584_, v___x_3585_, v_a_9731__boxed_3596_, v___y_9732__boxed_3597_, v_range_3588_, v_b_3589_, v_i_3590_, v_hs_3591_, v_hl_3592_, v___y_3593_, v___y_3594_);
lean_dec_ref(v___y_3594_);
lean_dec_ref(v_range_3588_);
lean_dec_ref(v_recInfos_3575_);
return v_res_3598_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___redArg(lean_object* v_inst_3599_){
_start:
{
lean_object* v_get_3600_; lean_object* v_set_3601_; lean_object* v___x_3602_; 
v_get_3600_ = lean_ctor_get(v_inst_3599_, 0);
v_set_3601_ = lean_ctor_get(v_inst_3599_, 1);
lean_inc(v_set_3601_);
lean_inc(v_get_3600_);
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v_get_3600_);
lean_ctor_set(v___x_3602_, 1, v_set_3601_);
return v___x_3602_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___redArg___boxed(lean_object* v_inst_3603_){
_start:
{
lean_object* v_res_3604_; 
v_res_3604_ = l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___redArg(v_inst_3603_);
lean_dec_ref(v_inst_3603_);
return v_res_3604_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean(lean_object* v_m_3605_, lean_object* v_inst_3606_){
_start:
{
lean_object* v___x_3607_; 
v___x_3607_ = l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___redArg(v_inst_3606_);
return v___x_3607_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean___boxed(lean_object* v_m_3608_, lean_object* v_inst_3609_){
_start:
{
lean_object* v_res_3610_; 
v_res_3610_ = l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorOfMonadStateOfNameGenerator__lean(v_m_3608_, v_inst_3609_);
lean_dec_ref(v_inst_3609_);
return v_res_3610_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_getNestedIfAuxCtor(lean_object* v_r_3611_, lean_object* v_env_x27_3612_, lean_object* v_c_3613_){
_start:
{
lean_object* v___x_3614_; 
v___x_3614_ = lean_environment_find(v_env_x27_3612_, v_c_3613_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v___x_3615_; 
v___x_3615_ = lean_box(0);
return v___x_3615_;
}
else
{
lean_object* v_val_3616_; 
v_val_3616_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_val_3616_);
lean_dec_ref(v___x_3614_);
if (lean_obj_tag(v_val_3616_) == 6)
{
lean_object* v_val_3617_; lean_object* v_induct_3618_; lean_object* v_aux2nested_3619_; lean_object* v___x_3620_; 
v_val_3617_ = lean_ctor_get(v_val_3616_, 0);
lean_inc_ref(v_val_3617_);
lean_dec_ref(v_val_3616_);
v_induct_3618_ = lean_ctor_get(v_val_3617_, 1);
lean_inc(v_induct_3618_);
lean_dec_ref(v_val_3617_);
v_aux2nested_3619_ = lean_ctor_get(v_r_3611_, 2);
v___x_3620_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_aux2nested_3619_, v_induct_3618_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v___x_3621_; 
lean_dec(v_induct_3618_);
v___x_3621_ = lean_box(0);
return v___x_3621_;
}
else
{
lean_object* v_val_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3630_; 
v_val_3622_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3624_ = v___x_3620_;
v_isShared_3625_ = v_isSharedCheck_3630_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_val_3622_);
lean_dec(v___x_3620_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3630_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3626_; lean_object* v___x_3628_; 
v___x_3626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3626_, 0, v_val_3622_);
lean_ctor_set(v___x_3626_, 1, v_induct_3618_);
if (v_isShared_3625_ == 0)
{
lean_ctor_set(v___x_3624_, 0, v___x_3626_);
v___x_3628_ = v___x_3624_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v___x_3626_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v___x_3631_; 
lean_dec(v_val_3616_);
v___x_3631_ = lean_box(0);
return v___x_3631_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_getNestedIfAuxCtor___boxed(lean_object* v_r_3632_, lean_object* v_env_x27_3633_, lean_object* v_c_3634_){
_start:
{
lean_object* v_res_3635_; 
v_res_3635_ = l_Lean4Lean_ElimNestedInductive_Result_getNestedIfAuxCtor(v_r_3632_, v_env_x27_3633_, v_c_3634_);
lean_dec_ref(v_r_3632_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0(lean_object* v_msg_3643_){
_start:
{
lean_object* v___f_3644_; lean_object* v___f_3645_; lean_object* v___f_3646_; lean_object* v___f_3647_; lean_object* v___f_3648_; lean_object* v___f_3649_; lean_object* v___f_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___f_3644_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__0));
v___f_3645_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__1));
v___f_3646_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__2));
v___f_3647_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__3));
v___f_3648_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__4));
v___f_3649_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__5));
v___f_3650_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__6));
v___x_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___f_3644_);
lean_ctor_set(v___x_3651_, 1, v___f_3645_);
v___x_3652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3651_);
lean_ctor_set(v___x_3652_, 1, v___f_3646_);
lean_ctor_set(v___x_3652_, 2, v___f_3647_);
lean_ctor_set(v___x_3652_, 3, v___f_3648_);
lean_ctor_set(v___x_3652_, 4, v___f_3649_);
v___x_3653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
lean_ctor_set(v___x_3653_, 1, v___f_3650_);
v___x_3654_ = lean_box(0);
v___x_3655_ = l_instInhabitedOfMonad___redArg(v___x_3653_, v___x_3654_);
v___x_3656_ = lean_panic_fn_borrowed(v___x_3655_, v_msg_3643_);
lean_dec(v___x_3655_);
return v___x_3656_;
}
}
static lean_object* _init_l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1___closed__0(void){
_start:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = lean_box(0);
v___x_3658_ = l_Lean_instInhabitedExpr;
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
lean_ctor_set(v___x_3659_, 1, v___x_3657_);
return v___x_3659_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1(lean_object* v_msg_3660_){
_start:
{
lean_object* v___x_3661_; lean_object* v___x_3662_; 
v___x_3661_ = lean_obj_once(&l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1___closed__0, &l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1___closed__0_once, _init_l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1___closed__0);
v___x_3662_ = lean_panic_fn_borrowed(v___x_3661_, v_msg_3660_);
return v___x_3662_;
}
}
static lean_object* _init_l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__2(void){
_start:
{
lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v___x_3665_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_3666_ = lean_unsigned_to_nat(33u);
v___x_3667_ = lean_unsigned_to_nat(516u);
v___x_3668_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__0));
v___x_3669_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_3670_ = l_mkPanicMessageWithDecl(v___x_3669_, v___x_3668_, v___x_3667_, v___x_3666_, v___x_3665_);
return v___x_3670_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName(lean_object* v_r_3671_, lean_object* v_env_x27_3672_, lean_object* v_c_3673_){
_start:
{
lean_object* v___y_3675_; lean_object* v___x_3683_; 
lean_inc(v_c_3673_);
v___x_3683_ = l_Lean4Lean_ElimNestedInductive_Result_getNestedIfAuxCtor(v_r_3671_, v_env_x27_3672_, v_c_3673_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_obj_once(&l_Lean4Lean_AddInductive_getIIndices___closed__3, &l_Lean4Lean_AddInductive_getIIndices___closed__3_once, _init_l_Lean4Lean_AddInductive_getIIndices___closed__3);
v___x_3685_ = l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__1(v___x_3684_);
v___y_3675_ = v___x_3685_;
goto v___jp_3674_;
}
else
{
lean_object* v_val_3686_; 
v_val_3686_ = lean_ctor_get(v___x_3683_, 0);
lean_inc(v_val_3686_);
lean_dec_ref(v___x_3683_);
v___y_3675_ = v_val_3686_;
goto v___jp_3674_;
}
v___jp_3674_:
{
lean_object* v_fst_3676_; lean_object* v_snd_3677_; lean_object* v___x_3678_; 
v_fst_3676_ = lean_ctor_get(v___y_3675_, 0);
lean_inc(v_fst_3676_);
v_snd_3677_ = lean_ctor_get(v___y_3675_, 1);
lean_inc(v_snd_3677_);
lean_dec_ref(v___y_3675_);
v___x_3678_ = l_Lean_Expr_getAppFn(v_fst_3676_);
lean_dec(v_fst_3676_);
if (lean_obj_tag(v___x_3678_) == 4)
{
lean_object* v_declName_3679_; lean_object* v___x_3680_; 
v_declName_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_declName_3679_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = l_Lean_Name_replacePrefix(v_c_3673_, v_snd_3677_, v_declName_3679_);
lean_dec(v_declName_3679_);
lean_dec(v_snd_3677_);
return v___x_3680_;
}
else
{
lean_object* v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref(v___x_3678_);
lean_dec(v_snd_3677_);
lean_dec(v_c_3673_);
v___x_3681_ = lean_obj_once(&l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__2, &l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__2_once, _init_l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__2);
v___x_3682_ = l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0(v___x_3681_);
return v___x_3682_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___boxed(lean_object* v_r_3687_, lean_object* v_env_x27_3688_, lean_object* v_c_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName(v_r_3687_, v_env_x27_3688_, v_c_3689_);
lean_dec_ref(v_r_3687_);
return v_res_3690_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__0(lean_object* v___y_3691_){
_start:
{
lean_object* v_namePrefix_3692_; lean_object* v_idx_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3704_; 
v_namePrefix_3692_ = lean_ctor_get(v___y_3691_, 0);
v_idx_3693_ = lean_ctor_get(v___y_3691_, 1);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___y_3691_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3695_ = v___y_3691_;
v_isShared_3696_ = v_isSharedCheck_3704_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_idx_3693_);
lean_inc(v_namePrefix_3692_);
lean_dec(v___y_3691_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3704_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v_r_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3701_; 
lean_inc(v_idx_3693_);
lean_inc(v_namePrefix_3692_);
v_r_3697_ = l_Lean_Name_num___override(v_namePrefix_3692_, v_idx_3693_);
v___x_3698_ = lean_unsigned_to_nat(1u);
v___x_3699_ = lean_nat_add(v_idx_3693_, v___x_3698_);
lean_dec(v_idx_3693_);
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 1, v___x_3699_);
v___x_3701_ = v___x_3695_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_namePrefix_3692_);
lean_ctor_set(v_reuseFailAlloc_3703_, 1, v___x_3699_);
v___x_3701_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
lean_object* v___x_3702_; 
v___x_3702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3702_, 0, v_r_3697_);
lean_ctor_set(v___x_3702_, 1, v___x_3701_);
return v___x_3702_;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__1(lean_object* v_msg_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v___f_3707_; lean_object* v___f_3708_; lean_object* v___f_3709_; lean_object* v___f_3710_; lean_object* v___f_3711_; lean_object* v___f_3712_; lean_object* v___f_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___f_3717_; lean_object* v___f_3718_; lean_object* v___f_3719_; lean_object* v___f_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_2494__overap_3729_; lean_object* v___x_3730_; 
v___f_3707_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__0));
v___f_3708_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__1));
v___f_3709_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__2));
v___f_3710_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__3));
v___f_3711_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__4));
v___f_3712_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__5));
v___f_3713_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__6));
v___x_3714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3714_, 0, v___f_3707_);
lean_ctor_set(v___x_3714_, 1, v___f_3708_);
v___x_3715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3714_);
lean_ctor_set(v___x_3715_, 1, v___f_3709_);
lean_ctor_set(v___x_3715_, 2, v___f_3710_);
lean_ctor_set(v___x_3715_, 3, v___f_3711_);
lean_ctor_set(v___x_3715_, 4, v___f_3712_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
lean_ctor_set(v___x_3716_, 1, v___f_3713_);
lean_inc_ref_n(v___x_3716_, 6);
v___f_3717_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__1), 6, 1);
lean_closure_set(v___f_3717_, 0, v___x_3716_);
v___f_3718_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__4), 6, 1);
lean_closure_set(v___f_3718_, 0, v___x_3716_);
v___f_3719_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__7), 6, 1);
lean_closure_set(v___f_3719_, 0, v___x_3716_);
v___f_3720_ = lean_alloc_closure((void*)(l_StateT_instMonad___redArg___lam__9), 6, 1);
lean_closure_set(v___f_3720_, 0, v___x_3716_);
v___x_3721_ = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(v___x_3721_, 0, lean_box(0));
lean_closure_set(v___x_3721_, 1, lean_box(0));
lean_closure_set(v___x_3721_, 2, v___x_3716_);
v___x_3722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3722_, 0, v___x_3721_);
lean_ctor_set(v___x_3722_, 1, v___f_3717_);
v___x_3723_ = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(v___x_3723_, 0, lean_box(0));
lean_closure_set(v___x_3723_, 1, lean_box(0));
lean_closure_set(v___x_3723_, 2, v___x_3716_);
v___x_3724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3722_);
lean_ctor_set(v___x_3724_, 1, v___x_3723_);
lean_ctor_set(v___x_3724_, 2, v___f_3718_);
lean_ctor_set(v___x_3724_, 3, v___f_3719_);
lean_ctor_set(v___x_3724_, 4, v___f_3720_);
v___x_3725_ = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(v___x_3725_, 0, lean_box(0));
lean_closure_set(v___x_3725_, 1, lean_box(0));
lean_closure_set(v___x_3725_, 2, v___x_3716_);
v___x_3726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3724_);
lean_ctor_set(v___x_3726_, 1, v___x_3725_);
v___x_3727_ = lean_box(0);
v___x_3728_ = l_instInhabitedOfMonad___redArg(v___x_3726_, v___x_3727_);
v___x_2494__overap_3729_ = lean_panic_fn_borrowed(v___x_3728_, v_msg_3705_);
lean_dec(v___x_3728_);
v___x_3730_ = lean_apply_1(v___x_2494__overap_3729_, v___y_3706_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__3(lean_object* v_msg_3731_){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
v___x_3732_ = lean_box(0);
v___x_3733_ = lean_panic_fn_borrowed(v___x_3732_, v_msg_3731_);
return v___x_3733_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__1(void){
_start:
{
lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3735_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_3736_ = lean_unsigned_to_nat(31u);
v___x_3737_ = lean_unsigned_to_nat(549u);
v___x_3738_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__0));
v___x_3739_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_3740_ = l_mkPanicMessageWithDecl(v___x_3739_, v___x_3738_, v___x_3737_, v___x_3736_, v___x_3735_);
return v___x_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4(lean_object* v_declName_3741_, lean_object* v_snd_3742_, lean_object* v___x_3743_, lean_object* v___x_3744_, lean_object* v___x_3745_, lean_object* v_x_3746_, lean_object* v_x_3747_, lean_object* v_x_3748_){
_start:
{
if (lean_obj_tag(v_x_3746_) == 5)
{
lean_object* v_fn_3749_; lean_object* v_arg_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; 
v_fn_3749_ = lean_ctor_get(v_x_3746_, 0);
lean_inc_ref(v_fn_3749_);
v_arg_3750_ = lean_ctor_get(v_x_3746_, 1);
lean_inc_ref(v_arg_3750_);
lean_dec_ref(v_x_3746_);
v___x_3751_ = lean_array_set(v_x_3747_, v_x_3748_, v_arg_3750_);
v___x_3752_ = lean_unsigned_to_nat(1u);
v___x_3753_ = lean_nat_sub(v_x_3748_, v___x_3752_);
lean_dec(v_x_3748_);
v_x_3746_ = v_fn_3749_;
v_x_3747_ = v___x_3751_;
v_x_3748_ = v___x_3753_;
goto _start;
}
else
{
lean_dec(v_x_3748_);
if (lean_obj_tag(v_x_3746_) == 4)
{
lean_object* v_declName_3755_; lean_object* v_us_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; 
v_declName_3755_ = lean_ctor_get(v_x_3746_, 0);
lean_inc(v_declName_3755_);
v_us_3756_ = lean_ctor_get(v_x_3746_, 1);
lean_inc(v_us_3756_);
lean_dec_ref(v_x_3746_);
v___x_3757_ = l_Lean_Name_replacePrefix(v_declName_3741_, v_snd_3742_, v_declName_3755_);
lean_dec(v_declName_3755_);
v___x_3758_ = l_Lean_Expr_const___override(v___x_3757_, v_us_3756_);
v___x_3759_ = l_Lean_mkAppN(v___x_3758_, v_x_3747_);
lean_dec_ref(v_x_3747_);
v___x_3760_ = l_Lean_mkAppRange(v___x_3759_, v___x_3743_, v___x_3744_, v___x_3745_);
v___x_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
return v___x_3761_;
}
else
{
lean_object* v___x_3762_; lean_object* v___x_3763_; 
lean_dec_ref(v_x_3747_);
lean_dec_ref(v_x_3746_);
lean_dec(v___x_3743_);
lean_dec(v_declName_3741_);
v___x_3762_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__1, &l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__1);
v___x_3763_ = l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__3(v___x_3762_);
return v___x_3763_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___boxed(lean_object* v_declName_3764_, lean_object* v_snd_3765_, lean_object* v___x_3766_, lean_object* v___x_3767_, lean_object* v___x_3768_, lean_object* v_x_3769_, lean_object* v_x_3770_, lean_object* v_x_3771_){
_start:
{
lean_object* v_res_3772_; 
v_res_3772_ = l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4(v_declName_3764_, v_snd_3765_, v___x_3766_, v___x_3767_, v___x_3768_, v_x_3769_, v_x_3770_, v_x_3771_);
lean_dec_ref(v___x_3768_);
lean_dec(v___x_3767_);
lean_dec(v_snd_3765_);
return v_res_3772_;
}
}
static lean_object* _init_l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; 
v___x_3774_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__0));
v___x_3775_ = lean_unsigned_to_nat(6u);
v___x_3776_ = lean_unsigned_to_nat(542u);
v___x_3777_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__0));
v___x_3778_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_3779_ = l_mkPanicMessageWithDecl(v___x_3778_, v___x_3777_, v___x_3776_, v___x_3775_, v___x_3774_);
return v___x_3779_;
}
}
static lean_object* _init_l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3781_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__2));
v___x_3782_ = lean_unsigned_to_nat(4u);
v___x_3783_ = lean_unsigned_to_nat(546u);
v___x_3784_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__0));
v___x_3785_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_3786_ = l_mkPanicMessageWithDecl(v___x_3785_, v___x_3784_, v___x_3783_, v___x_3782_, v___x_3781_);
return v___x_3786_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0(lean_object* v_aux2nested_3787_, lean_object* v___x_3788_, lean_object* v_nparams_3789_, lean_object* v_fst_3790_, lean_object* v_r_3791_, lean_object* v_env_x27_3792_, lean_object* v_auxRec_3793_, lean_object* v_t_3794_){
_start:
{
if (lean_obj_tag(v_t_3794_) == 4)
{
lean_object* v_declName_3838_; lean_object* v_us_3839_; lean_object* v___x_3840_; 
v_declName_3838_ = lean_ctor_get(v_t_3794_, 0);
v_us_3839_ = lean_ctor_get(v_t_3794_, 1);
v___x_3840_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_auxRec_3793_, v_declName_3838_);
if (lean_obj_tag(v___x_3840_) == 1)
{
lean_object* v_val_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3849_; 
lean_inc(v_us_3839_);
lean_dec_ref(v_t_3794_);
lean_dec_ref(v_env_x27_3792_);
lean_dec(v_nparams_3789_);
v_val_3841_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3843_ = v___x_3840_;
v_isShared_3844_ = v_isSharedCheck_3849_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_val_3841_);
lean_dec(v___x_3840_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3849_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3845_ = l_Lean_Expr_const___override(v_val_3841_, v_us_3839_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3845_);
v___x_3847_ = v___x_3843_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3845_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
else
{
lean_dec(v___x_3840_);
goto v___jp_3795_;
}
}
else
{
goto v___jp_3795_;
}
v___jp_3795_:
{
lean_object* v___x_3796_; 
v___x_3796_ = l_Lean_Expr_getAppFn(v_t_3794_);
if (lean_obj_tag(v___x_3796_) == 4)
{
lean_object* v_declName_3797_; lean_object* v___x_3798_; 
v_declName_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_declName_3797_);
lean_dec_ref(v___x_3796_);
v___x_3798_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_aux2nested_3787_, v_declName_3797_);
if (lean_obj_tag(v___x_3798_) == 1)
{
lean_object* v_val_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3817_; 
lean_dec(v_declName_3797_);
lean_dec_ref(v_env_x27_3792_);
v_val_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3817_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3817_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3817_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_val_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3817_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v_dummy_3803_; lean_object* v_nargs_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; uint8_t v___x_3809_; 
v_dummy_3803_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
v_nargs_3804_ = l_Lean_Expr_getAppNumArgs(v_t_3794_);
lean_inc(v_nargs_3804_);
v___x_3805_ = lean_mk_array(v_nargs_3804_, v_dummy_3803_);
v___x_3806_ = lean_nat_sub(v_nargs_3804_, v___x_3788_);
lean_dec(v_nargs_3804_);
v___x_3807_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_3794_, v___x_3805_, v___x_3806_);
v___x_3808_ = lean_array_get_size(v___x_3807_);
v___x_3809_ = lean_nat_dec_le(v_nparams_3789_, v___x_3808_);
if (v___x_3809_ == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3811_; 
lean_dec_ref(v___x_3807_);
lean_del_object(v___x_3801_);
lean_dec(v_val_3799_);
lean_dec(v_nparams_3789_);
v___x_3810_ = lean_obj_once(&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__1, &l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__1_once, _init_l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__1);
v___x_3811_ = l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__3(v___x_3810_);
return v___x_3811_;
}
else
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3815_; 
v___x_3812_ = lean_expr_instantiate_rev(v_val_3799_, v_fst_3790_);
lean_dec(v_val_3799_);
v___x_3813_ = l_Lean_mkAppRange(v___x_3812_, v_nparams_3789_, v___x_3808_, v___x_3807_);
lean_dec_ref(v___x_3807_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3813_);
v___x_3815_ = v___x_3801_;
goto v_reusejp_3814_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3813_);
v___x_3815_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3814_;
}
v_reusejp_3814_:
{
return v___x_3815_;
}
}
}
}
else
{
lean_object* v___x_3818_; 
lean_dec(v___x_3798_);
lean_inc(v_declName_3797_);
v___x_3818_ = l_Lean4Lean_ElimNestedInductive_Result_getNestedIfAuxCtor(v_r_3791_, v_env_x27_3792_, v_declName_3797_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v___x_3819_; 
lean_dec(v_declName_3797_);
lean_dec_ref(v_t_3794_);
lean_dec(v_nparams_3789_);
v___x_3819_ = lean_box(0);
return v___x_3819_;
}
else
{
lean_object* v_val_3820_; lean_object* v_fst_3821_; lean_object* v_snd_3822_; lean_object* v_dummy_3823_; lean_object* v_nargs_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; uint8_t v___x_3829_; 
v_val_3820_ = lean_ctor_get(v___x_3818_, 0);
lean_inc(v_val_3820_);
lean_dec_ref(v___x_3818_);
v_fst_3821_ = lean_ctor_get(v_val_3820_, 0);
lean_inc(v_fst_3821_);
v_snd_3822_ = lean_ctor_get(v_val_3820_, 1);
lean_inc(v_snd_3822_);
lean_dec(v_val_3820_);
v_dummy_3823_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
v_nargs_3824_ = l_Lean_Expr_getAppNumArgs(v_t_3794_);
lean_inc(v_nargs_3824_);
v___x_3825_ = lean_mk_array(v_nargs_3824_, v_dummy_3823_);
v___x_3826_ = lean_nat_sub(v_nargs_3824_, v___x_3788_);
lean_dec(v_nargs_3824_);
v___x_3827_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_t_3794_, v___x_3825_, v___x_3826_);
v___x_3828_ = lean_array_get_size(v___x_3827_);
v___x_3829_ = lean_nat_dec_le(v_nparams_3789_, v___x_3828_);
if (v___x_3829_ == 0)
{
lean_object* v___x_3830_; lean_object* v___x_3831_; 
lean_dec_ref(v___x_3827_);
lean_dec(v_snd_3822_);
lean_dec(v_fst_3821_);
lean_dec(v_declName_3797_);
lean_dec(v_nparams_3789_);
v___x_3830_ = lean_obj_once(&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__3, &l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__3_once, _init_l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___closed__3);
v___x_3831_ = l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__3(v___x_3830_);
return v___x_3831_;
}
else
{
lean_object* v___x_3832_; lean_object* v_nargs_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3832_ = lean_expr_instantiate_rev(v_fst_3821_, v_fst_3790_);
lean_dec(v_fst_3821_);
v_nargs_3833_ = l_Lean_Expr_getAppNumArgs(v___x_3832_);
lean_inc(v_nargs_3833_);
v___x_3834_ = lean_mk_array(v_nargs_3833_, v_dummy_3823_);
v___x_3835_ = lean_nat_sub(v_nargs_3833_, v___x_3788_);
lean_dec(v_nargs_3833_);
v___x_3836_ = l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4(v_declName_3797_, v_snd_3822_, v_nparams_3789_, v___x_3828_, v___x_3827_, v___x_3832_, v___x_3834_, v___x_3835_);
lean_dec_ref(v___x_3827_);
lean_dec(v_snd_3822_);
return v___x_3836_;
}
}
}
}
else
{
lean_object* v___x_3837_; 
lean_dec_ref(v___x_3796_);
lean_dec_ref(v_t_3794_);
lean_dec_ref(v_env_x27_3792_);
lean_dec(v_nparams_3789_);
v___x_3837_ = lean_box(0);
return v___x_3837_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___boxed(lean_object* v_aux2nested_3850_, lean_object* v___x_3851_, lean_object* v_nparams_3852_, lean_object* v_fst_3853_, lean_object* v_r_3854_, lean_object* v_env_x27_3855_, lean_object* v_auxRec_3856_, lean_object* v_t_3857_){
_start:
{
lean_object* v_res_3858_; 
v_res_3858_ = l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0(v_aux2nested_3850_, v___x_3851_, v_nparams_3852_, v_fst_3853_, v_r_3854_, v_env_x27_3855_, v_auxRec_3856_, v_t_3857_);
lean_dec(v_auxRec_3856_);
lean_dec_ref(v_r_3854_);
lean_dec(v_fst_3853_);
lean_dec(v___x_3851_);
lean_dec(v_aux2nested_3850_);
return v_res_3858_;
}
}
static lean_object* _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; 
v___x_3859_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_3860_ = lean_unsigned_to_nat(11u);
v___x_3861_ = lean_unsigned_to_nat(534u);
v___x_3862_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__4___closed__0));
v___x_3863_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_3864_ = l_mkPanicMessageWithDecl(v___x_3863_, v___x_3862_, v___x_3861_, v___x_3860_, v___x_3859_);
return v___x_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg(lean_object* v_range_3865_, lean_object* v_b_3866_, lean_object* v_i_3867_, lean_object* v___y_3868_){
_start:
{
lean_object* v_stop_3869_; lean_object* v_step_3870_; lean_object* v_a_3872_; lean_object* v_snd_3873_; uint8_t v___x_3876_; 
v_stop_3869_ = lean_ctor_get(v_range_3865_, 1);
v_step_3870_ = lean_ctor_get(v_range_3865_, 2);
v___x_3876_ = lean_nat_dec_lt(v_i_3867_, v_stop_3869_);
if (v___x_3876_ == 0)
{
lean_object* v___x_3877_; 
lean_dec(v_i_3867_);
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v_b_3866_);
lean_ctor_set(v___x_3877_, 1, v___y_3868_);
return v___x_3877_;
}
else
{
lean_object* v_snd_3878_; lean_object* v_fst_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3935_; 
v_snd_3878_ = lean_ctor_get(v_b_3866_, 1);
v_fst_3879_ = lean_ctor_get(v_b_3866_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v_b_3866_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3881_ = v_b_3866_;
v_isShared_3882_ = v_isSharedCheck_3935_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_snd_3878_);
lean_inc(v_fst_3879_);
lean_dec(v_b_3866_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3935_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v_fst_3883_; lean_object* v_snd_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3934_; 
v_fst_3883_ = lean_ctor_get(v_snd_3878_, 0);
v_snd_3884_ = lean_ctor_get(v_snd_3878_, 1);
v_isSharedCheck_3934_ = !lean_is_exclusive(v_snd_3878_);
if (v_isSharedCheck_3934_ == 0)
{
v___x_3886_ = v_snd_3878_;
v_isShared_3887_ = v_isSharedCheck_3934_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_snd_3884_);
lean_inc(v_fst_3883_);
lean_dec(v_snd_3878_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3934_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v_name_3889_; lean_object* v_dom_3890_; lean_object* v_body_3891_; uint8_t v_bi_3892_; lean_object* v___y_3893_; 
switch(lean_obj_tag(v_fst_3879_))
{
case 7:
{
lean_object* v_binderName_3912_; lean_object* v_binderType_3913_; lean_object* v_body_3914_; uint8_t v_binderInfo_3915_; 
lean_del_object(v___x_3881_);
v_binderName_3912_ = lean_ctor_get(v_fst_3879_, 0);
lean_inc(v_binderName_3912_);
v_binderType_3913_ = lean_ctor_get(v_fst_3879_, 1);
lean_inc_ref(v_binderType_3913_);
v_body_3914_ = lean_ctor_get(v_fst_3879_, 2);
lean_inc_ref(v_body_3914_);
v_binderInfo_3915_ = lean_ctor_get_uint8(v_fst_3879_, sizeof(void*)*3 + 8);
lean_dec_ref(v_fst_3879_);
v_name_3889_ = v_binderName_3912_;
v_dom_3890_ = v_binderType_3913_;
v_body_3891_ = v_body_3914_;
v_bi_3892_ = v_binderInfo_3915_;
v___y_3893_ = v___y_3868_;
goto v___jp_3888_;
}
case 6:
{
lean_object* v_binderName_3916_; lean_object* v_binderType_3917_; lean_object* v_body_3918_; uint8_t v_binderInfo_3919_; 
lean_del_object(v___x_3881_);
v_binderName_3916_ = lean_ctor_get(v_fst_3879_, 0);
lean_inc(v_binderName_3916_);
v_binderType_3917_ = lean_ctor_get(v_fst_3879_, 1);
lean_inc_ref(v_binderType_3917_);
v_body_3918_ = lean_ctor_get(v_fst_3879_, 2);
lean_inc_ref(v_body_3918_);
v_binderInfo_3919_ = lean_ctor_get_uint8(v_fst_3879_, sizeof(void*)*3 + 8);
lean_dec_ref(v_fst_3879_);
v_name_3889_ = v_binderName_3916_;
v_dom_3890_ = v_binderType_3917_;
v_body_3891_ = v_body_3918_;
v_bi_3892_ = v_binderInfo_3919_;
v___y_3893_ = v___y_3868_;
goto v___jp_3888_;
}
default: 
{
lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v_snd_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3932_; 
lean_del_object(v___x_3886_);
v___x_3920_ = lean_obj_once(&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___closed__0, &l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___closed__0_once, _init_l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___closed__0);
v___x_3921_ = l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__1(v___x_3920_, v___y_3868_);
v_snd_3922_ = lean_ctor_get(v___x_3921_, 1);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3921_);
if (v_isSharedCheck_3932_ == 0)
{
lean_object* v_unused_3933_; 
v_unused_3933_ = lean_ctor_get(v___x_3921_, 0);
lean_dec(v_unused_3933_);
v___x_3924_ = v___x_3921_;
v_isShared_3925_ = v_isSharedCheck_3932_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_snd_3922_);
lean_dec(v___x_3921_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3932_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 1, v_snd_3884_);
lean_ctor_set(v___x_3924_, 0, v_fst_3883_);
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_fst_3883_);
lean_ctor_set(v_reuseFailAlloc_3931_, 1, v_snd_3884_);
v___x_3927_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
lean_object* v___x_3929_; 
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v___x_3927_);
v___x_3929_ = v___x_3881_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_fst_3879_);
lean_ctor_set(v_reuseFailAlloc_3930_, 1, v___x_3927_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
v_a_3872_ = v___x_3929_;
v_snd_3873_ = v_snd_3922_;
goto v___jp_3871_;
}
}
}
}
}
v___jp_3888_:
{
lean_object* v___x_3894_; lean_object* v_fst_3895_; lean_object* v_snd_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3911_; 
v___x_3894_ = l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__0(v___y_3893_);
v_fst_3895_ = lean_ctor_get(v___x_3894_, 0);
v_snd_3896_ = lean_ctor_get(v___x_3894_, 1);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3898_ = v___x_3894_;
v_isShared_3899_ = v_isSharedCheck_3911_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_snd_3896_);
lean_inc(v_fst_3895_);
lean_dec(v___x_3894_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3911_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
uint8_t v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; lean_object* v___x_3903_; lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3900_ = 0;
lean_inc(v_fst_3895_);
v___x_3901_ = l_Lean_LocalContext_mkLocalDecl(v_snd_3884_, v_fst_3895_, v_name_3889_, v_dom_3890_, v_bi_3892_, v___x_3900_);
v___x_3902_ = l_Lean_Expr_fvar___override(v_fst_3895_);
v___x_3903_ = lean_expr_instantiate1(v_body_3891_, v___x_3902_);
lean_dec_ref(v_body_3891_);
v___x_3904_ = lean_array_push(v_fst_3883_, v___x_3902_);
if (v_isShared_3899_ == 0)
{
lean_ctor_set(v___x_3898_, 1, v___x_3901_);
lean_ctor_set(v___x_3898_, 0, v___x_3904_);
v___x_3906_ = v___x_3898_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3904_);
lean_ctor_set(v_reuseFailAlloc_3910_, 1, v___x_3901_);
v___x_3906_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3908_; 
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 1, v___x_3906_);
lean_ctor_set(v___x_3886_, 0, v___x_3903_);
v___x_3908_ = v___x_3886_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3903_);
lean_ctor_set(v_reuseFailAlloc_3909_, 1, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
v_a_3872_ = v___x_3908_;
v_snd_3873_ = v_snd_3896_;
goto v___jp_3871_;
}
}
}
}
}
}
}
v___jp_3871_:
{
lean_object* v___x_3874_; 
v___x_3874_ = lean_nat_add(v_i_3867_, v_step_3870_);
lean_dec(v_i_3867_);
v_b_3866_ = v_a_3872_;
v_i_3867_ = v___x_3874_;
v___y_3868_ = v_snd_3873_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg___boxed(lean_object* v_range_3936_, lean_object* v_b_3937_, lean_object* v_i_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v_res_3940_; 
v_res_3940_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg(v_range_3936_, v_b_3937_, v_i_3938_, v___y_3939_);
lean_dec_ref(v_range_3936_);
return v_res_3940_;
}
}
static lean_object* _init_l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__0(void){
_start:
{
lean_object* v_lctx_3941_; lean_object* v_As_3942_; lean_object* v___x_3943_; 
v_lctx_3941_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4);
v_As_3942_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
v___x_3943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3943_, 0, v_As_3942_);
lean_ctor_set(v___x_3943_, 1, v_lctx_3941_);
return v___x_3943_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_Result_restoreNested(lean_object* v_r_3950_, lean_object* v_env_x27_3951_, lean_object* v_e_3952_, lean_object* v_auxRec_3953_){
_start:
{
lean_object* v___x_3954_; lean_object* v_nparams_3955_; lean_object* v_aux2nested_3956_; uint8_t v_pi_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v_fst_3964_; lean_object* v_snd_3965_; lean_object* v_fst_3966_; lean_object* v_fst_3967_; lean_object* v_snd_3968_; lean_object* v___f_3969_; lean_object* v___x_3970_; uint8_t v___x_3971_; 
v___x_3954_ = lean_unsigned_to_nat(0u);
v_nparams_3955_ = lean_ctor_get(v_r_3950_, 1);
lean_inc_n(v_nparams_3955_, 2);
v_aux2nested_3956_ = lean_ctor_get(v_r_3950_, 2);
lean_inc(v_aux2nested_3956_);
v_pi_3957_ = l_Lean_Expr_isForall(v_e_3952_);
v___x_3958_ = lean_unsigned_to_nat(1u);
v___x_3959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3954_);
lean_ctor_set(v___x_3959_, 1, v_nparams_3955_);
lean_ctor_set(v___x_3959_, 2, v___x_3958_);
v___x_3960_ = lean_obj_once(&l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__0, &l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__0_once, _init_l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__0);
v___x_3961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3961_, 0, v_e_3952_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__3));
v___x_3963_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg(v___x_3959_, v___x_3961_, v___x_3954_, v___x_3962_);
lean_dec_ref(v___x_3959_);
v_fst_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_fst_3964_);
lean_dec_ref(v___x_3963_);
v_snd_3965_ = lean_ctor_get(v_fst_3964_, 1);
lean_inc(v_snd_3965_);
v_fst_3966_ = lean_ctor_get(v_fst_3964_, 0);
lean_inc(v_fst_3966_);
lean_dec(v_fst_3964_);
v_fst_3967_ = lean_ctor_get(v_snd_3965_, 0);
lean_inc_n(v_fst_3967_, 2);
v_snd_3968_ = lean_ctor_get(v_snd_3965_, 1);
lean_inc(v_snd_3968_);
lean_dec(v_snd_3965_);
v___f_3969_ = lean_alloc_closure((void*)(l_Lean4Lean_ElimNestedInductive_Result_restoreNested___lam__0___boxed), 8, 7);
lean_closure_set(v___f_3969_, 0, v_aux2nested_3956_);
lean_closure_set(v___f_3969_, 1, v___x_3958_);
lean_closure_set(v___f_3969_, 2, v_nparams_3955_);
lean_closure_set(v___f_3969_, 3, v_fst_3967_);
lean_closure_set(v___f_3969_, 4, v_r_3950_);
lean_closure_set(v___f_3969_, 5, v_env_x27_3951_);
lean_closure_set(v___f_3969_, 6, v_auxRec_3953_);
v___x_3970_ = lean_replace_expr(v___f_3969_, v_fst_3966_);
lean_dec(v_fst_3966_);
lean_dec_ref(v___f_3969_);
v___x_3971_ = 1;
if (v_pi_3957_ == 0)
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_LocalContext_mkLambda(v_snd_3968_, v_fst_3967_, v___x_3970_, v___x_3971_, v_pi_3957_);
lean_dec_ref(v___x_3970_);
lean_dec(v_fst_3967_);
return v___x_3972_;
}
else
{
uint8_t v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = 0;
v___x_3974_ = l_Lean_LocalContext_mkForall(v_snd_3968_, v_fst_3967_, v___x_3970_, v___x_3971_, v___x_3973_);
lean_dec_ref(v___x_3970_);
lean_dec(v_fst_3967_);
return v___x_3974_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2(lean_object* v_range_3975_, lean_object* v_b_3976_, lean_object* v_i_3977_, lean_object* v_hs_3978_, lean_object* v_hl_3979_, lean_object* v___y_3980_){
_start:
{
lean_object* v___x_3981_; 
v___x_3981_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___redArg(v_range_3975_, v_b_3976_, v_i_3977_, v___y_3980_);
return v___x_3981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2___boxed(lean_object* v_range_3982_, lean_object* v_b_3983_, lean_object* v_i_3984_, lean_object* v_hs_3985_, lean_object* v_hl_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_res_3988_; 
v_res_3988_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_Result_restoreNested_spec__2(v_range_3982_, v_b_3983_, v_i_3984_, v_hs_3985_, v_hl_3986_, v___y_3987_);
lean_dec_ref(v_range_3982_);
return v_res_3988_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__0(lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
lean_inc_ref(v___y_3999_);
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___y_3999_);
lean_ctor_set(v___x_4000_, 1, v___y_3999_);
v___x_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4001_, 0, v___x_4000_);
return v___x_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__0___boxed(lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v_res_4004_; 
v_res_4004_ = l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__0(v___y_4002_, v___y_4003_);
lean_dec_ref(v___y_4002_);
return v_res_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__1(lean_object* v_____do__lift_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_ngen_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; 
v_ngen_4008_ = lean_ctor_get(v_____do__lift_4005_, 0);
lean_inc_ref(v_ngen_4008_);
v___x_4009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4009_, 0, v_ngen_4008_);
lean_ctor_set(v___x_4009_, 1, v___y_4007_);
v___x_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4010_, 0, v___x_4009_);
return v___x_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__1___boxed(lean_object* v_____do__lift_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v_res_4014_; 
v_res_4014_ = l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__1(v_____do__lift_4011_, v___y_4012_, v___y_4013_);
lean_dec_ref(v___y_4012_);
lean_dec_ref(v_____do__lift_4011_);
return v_res_4014_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__2(lean_object* v_ngen_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_nestedAux_4018_; lean_object* v_lvls_4019_; lean_object* v_newTypes_4020_; lean_object* v_nextIdx_4021_; lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4031_; 
v_nestedAux_4018_ = lean_ctor_get(v___y_4017_, 1);
v_lvls_4019_ = lean_ctor_get(v___y_4017_, 2);
v_newTypes_4020_ = lean_ctor_get(v___y_4017_, 3);
v_nextIdx_4021_ = lean_ctor_get(v___y_4017_, 4);
v_isSharedCheck_4031_ = !lean_is_exclusive(v___y_4017_);
if (v_isSharedCheck_4031_ == 0)
{
lean_object* v_unused_4032_; 
v_unused_4032_ = lean_ctor_get(v___y_4017_, 0);
lean_dec(v_unused_4032_);
v___x_4023_ = v___y_4017_;
v_isShared_4024_ = v_isSharedCheck_4031_;
goto v_resetjp_4022_;
}
else
{
lean_inc(v_nextIdx_4021_);
lean_inc(v_newTypes_4020_);
lean_inc(v_lvls_4019_);
lean_inc(v_nestedAux_4018_);
lean_dec(v___y_4017_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4031_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4025_ = lean_box(0);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v_ngen_4015_);
v___x_4027_ = v___x_4023_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4030_; 
v_reuseFailAlloc_4030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4030_, 0, v_ngen_4015_);
lean_ctor_set(v_reuseFailAlloc_4030_, 1, v_nestedAux_4018_);
lean_ctor_set(v_reuseFailAlloc_4030_, 2, v_lvls_4019_);
lean_ctor_set(v_reuseFailAlloc_4030_, 3, v_newTypes_4020_);
lean_ctor_set(v_reuseFailAlloc_4030_, 4, v_nextIdx_4021_);
v___x_4027_ = v_reuseFailAlloc_4030_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4025_);
lean_ctor_set(v___x_4028_, 1, v___x_4027_);
v___x_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
return v___x_4029_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__2___boxed(lean_object* v_ngen_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
lean_object* v_res_4036_; 
v_res_4036_ = l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___lam__2(v_ngen_4033_, v___y_4034_, v___y_4035_);
lean_dec_ref(v___y_4034_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName_loop(lean_object* v_n_4074_, lean_object* v_env_4075_, lean_object* v_s_4076_, lean_object* v_i_4077_){
_start:
{
lean_object* v_r_4078_; uint8_t v___x_4079_; 
lean_inc(v_i_4077_);
lean_inc(v_n_4074_);
v_r_4078_ = lean_name_append_index_after(v_n_4074_, v_i_4077_);
v___x_4079_ = l_Lean_Kernel_Environment_contains(v_env_4075_, v_r_4078_);
if (v___x_4079_ == 0)
{
lean_object* v_ngen_4080_; lean_object* v_nestedAux_4081_; lean_object* v_lvls_4082_; lean_object* v_newTypes_4083_; lean_object* v___x_4085_; uint8_t v_isShared_4086_; uint8_t v_isSharedCheck_4094_; 
lean_dec(v_n_4074_);
v_ngen_4080_ = lean_ctor_get(v_s_4076_, 0);
v_nestedAux_4081_ = lean_ctor_get(v_s_4076_, 1);
v_lvls_4082_ = lean_ctor_get(v_s_4076_, 2);
v_newTypes_4083_ = lean_ctor_get(v_s_4076_, 3);
v_isSharedCheck_4094_ = !lean_is_exclusive(v_s_4076_);
if (v_isSharedCheck_4094_ == 0)
{
lean_object* v_unused_4095_; 
v_unused_4095_ = lean_ctor_get(v_s_4076_, 4);
lean_dec(v_unused_4095_);
v___x_4085_ = v_s_4076_;
v_isShared_4086_ = v_isSharedCheck_4094_;
goto v_resetjp_4084_;
}
else
{
lean_inc(v_newTypes_4083_);
lean_inc(v_lvls_4082_);
lean_inc(v_nestedAux_4081_);
lean_inc(v_ngen_4080_);
lean_dec(v_s_4076_);
v___x_4085_ = lean_box(0);
v_isShared_4086_ = v_isSharedCheck_4094_;
goto v_resetjp_4084_;
}
v_resetjp_4084_:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4087_ = lean_unsigned_to_nat(1u);
v___x_4088_ = lean_nat_add(v_i_4077_, v___x_4087_);
lean_dec(v_i_4077_);
if (v_isShared_4086_ == 0)
{
lean_ctor_set(v___x_4085_, 4, v___x_4088_);
v___x_4090_ = v___x_4085_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4093_; 
v_reuseFailAlloc_4093_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_ngen_4080_);
lean_ctor_set(v_reuseFailAlloc_4093_, 1, v_nestedAux_4081_);
lean_ctor_set(v_reuseFailAlloc_4093_, 2, v_lvls_4082_);
lean_ctor_set(v_reuseFailAlloc_4093_, 3, v_newTypes_4083_);
lean_ctor_set(v_reuseFailAlloc_4093_, 4, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4093_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; 
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v_r_4078_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
return v___x_4092_;
}
}
}
else
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
lean_dec(v_r_4078_);
v___x_4096_ = lean_unsigned_to_nat(1u);
v___x_4097_ = lean_nat_add(v_i_4077_, v___x_4096_);
lean_dec(v_i_4077_);
v_i_4077_ = v___x_4097_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName_loop___boxed(lean_object* v_n_4099_, lean_object* v_env_4100_, lean_object* v_s_4101_, lean_object* v_i_4102_){
_start:
{
lean_object* v_res_4103_; 
v_res_4103_ = l_Lean4Lean_ElimNestedInductive_mkUniqueName_loop(v_n_4099_, v_env_4100_, v_s_4101_, v_i_4102_);
lean_dec_ref(v_env_4100_);
return v_res_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName(lean_object* v_n_4104_, lean_object* v_env_4105_, lean_object* v_s_4106_){
_start:
{
lean_object* v_nextIdx_4107_; lean_object* v___x_4108_; 
v_nextIdx_4107_ = lean_ctor_get(v_s_4106_, 4);
lean_inc(v_nextIdx_4107_);
v___x_4108_ = l_Lean4Lean_ElimNestedInductive_mkUniqueName_loop(v_n_4104_, v_env_4105_, v_s_4106_, v_nextIdx_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_mkUniqueName___boxed(lean_object* v_n_4109_, lean_object* v_env_4110_, lean_object* v_s_4111_){
_start:
{
lean_object* v_res_4112_; 
v_res_4112_ = l_Lean4Lean_ElimNestedInductive_mkUniqueName(v_n_4109_, v_env_4110_, v_s_4111_);
lean_dec_ref(v_env_4110_);
return v_res_4112_;
}
}
static lean_object* _init_l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4117_ = l_Lean_instInhabitedExpr;
v___x_4118_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12));
v___x_4119_ = l_instInhabitedOfMonad___redArg(v___x_4118_, v___x_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0(lean_object* v_msg_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v___x_4123_; lean_object* v___f_4124_; lean_object* v___x_354__overap_4125_; lean_object* v___x_4126_; 
v___x_4123_ = lean_obj_once(&l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___closed__0, &l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___closed__0_once, _init_l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___closed__0);
v___f_4124_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4124_, 0, v___x_4123_);
v___x_354__overap_4125_ = lean_panic_fn_borrowed(v___f_4124_, v_msg_4120_);
lean_dec_ref(v___f_4124_);
lean_inc_ref(v___y_4121_);
v___x_4126_ = lean_apply_2(v___x_354__overap_4125_, v___y_4121_, v___y_4122_);
return v___x_4126_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0___boxed(lean_object* v_msg_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_){
_start:
{
lean_object* v_res_4130_; 
v_res_4130_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0(v_msg_4127_, v___y_4128_, v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4130_;
}
}
static lean_object* _init_l_Lean4Lean_ElimNestedInductive_replaceParams___closed__2(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; 
v___x_4133_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_replaceParams___closed__1));
v___x_4134_ = lean_unsigned_to_nat(2u);
v___x_4135_ = lean_unsigned_to_nat(584u);
v___x_4136_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_replaceParams___closed__0));
v___x_4137_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_4138_ = l_mkPanicMessageWithDecl(v___x_4137_, v___x_4136_, v___x_4135_, v___x_4134_, v___x_4133_);
return v___x_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceParams(lean_object* v_params_4139_, lean_object* v_e_4140_, lean_object* v_As_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
lean_object* v___x_4144_; lean_object* v___x_4145_; uint8_t v___x_4146_; 
v___x_4144_ = lean_array_get_size(v_As_4141_);
v___x_4145_ = lean_array_get_size(v_params_4139_);
v___x_4146_ = lean_nat_dec_eq(v___x_4144_, v___x_4145_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_obj_once(&l_Lean4Lean_ElimNestedInductive_replaceParams___closed__2, &l_Lean4Lean_ElimNestedInductive_replaceParams___closed__2_once, _init_l_Lean4Lean_ElimNestedInductive_replaceParams___closed__2);
v___x_4148_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceParams_spec__0(v___x_4147_, v_a_4142_, v_a_4143_);
return v___x_4148_;
}
else
{
lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; lean_object* v___x_4152_; 
v___x_4149_ = lean_expr_abstract(v_e_4140_, v_As_4141_);
v___x_4150_ = lean_expr_instantiate_rev(v___x_4149_, v_params_4139_);
lean_dec_ref(v___x_4149_);
v___x_4151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
lean_ctor_set(v___x_4151_, 1, v_a_4143_);
v___x_4152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
return v___x_4152_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceParams___boxed(lean_object* v_params_4153_, lean_object* v_e_4154_, lean_object* v_As_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean4Lean_ElimNestedInductive_replaceParams(v_params_4153_, v_e_4154_, v_As_4155_, v_a_4156_, v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec_ref(v_As_4155_);
lean_dec_ref(v_e_4154_);
lean_dec_ref(v_params_4153_);
return v_res_4158_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__0(lean_object* v_declName_4159_, lean_object* v_as_4160_, size_t v_i_4161_, size_t v_stop_4162_){
_start:
{
uint8_t v___x_4163_; 
v___x_4163_ = lean_usize_dec_eq(v_i_4161_, v_stop_4162_);
if (v___x_4163_ == 0)
{
lean_object* v___x_4164_; lean_object* v_name_4165_; uint8_t v___x_4166_; 
v___x_4164_ = lean_array_uget_borrowed(v_as_4160_, v_i_4161_);
v_name_4165_ = lean_ctor_get(v___x_4164_, 0);
v___x_4166_ = lean_name_eq(v_declName_4159_, v_name_4165_);
if (v___x_4166_ == 0)
{
size_t v___x_4167_; size_t v___x_4168_; 
v___x_4167_ = ((size_t)1ULL);
v___x_4168_ = lean_usize_add(v_i_4161_, v___x_4167_);
v_i_4161_ = v___x_4168_;
goto _start;
}
else
{
return v___x_4166_;
}
}
else
{
uint8_t v___x_4170_; 
v___x_4170_ = 0;
return v___x_4170_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__0___boxed(lean_object* v_declName_4171_, lean_object* v_as_4172_, lean_object* v_i_4173_, lean_object* v_stop_4174_){
_start:
{
size_t v_i_boxed_4175_; size_t v_stop_boxed_4176_; uint8_t v_res_4177_; lean_object* v_r_4178_; 
v_i_boxed_4175_ = lean_unbox_usize(v_i_4173_);
lean_dec(v_i_4173_);
v_stop_boxed_4176_ = lean_unbox_usize(v_stop_4174_);
lean_dec(v_stop_4174_);
v_res_4177_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__0(v_declName_4171_, v_as_4172_, v_i_boxed_4175_, v_stop_boxed_4176_);
lean_dec_ref(v_as_4172_);
lean_dec(v_declName_4171_);
v_r_4178_ = lean_box(v_res_4177_);
return v_r_4178_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___lam__0(lean_object* v_newTypes_4179_, lean_object* v___x_4180_, uint8_t v___x_4181_, lean_object* v_x_4182_){
_start:
{
if (lean_obj_tag(v_x_4182_) == 4)
{
lean_object* v_declName_4183_; lean_object* v___x_4184_; uint8_t v___x_4185_; 
v_declName_4183_ = lean_ctor_get(v_x_4182_, 0);
v___x_4184_ = lean_array_get_size(v_newTypes_4179_);
v___x_4185_ = lean_nat_dec_lt(v___x_4180_, v___x_4184_);
if (v___x_4185_ == 0)
{
return v___x_4181_;
}
else
{
if (v___x_4185_ == 0)
{
return v___x_4181_;
}
else
{
size_t v___x_4186_; size_t v___x_4187_; uint8_t v___x_4188_; 
v___x_4186_ = ((size_t)0ULL);
v___x_4187_ = lean_usize_of_nat(v___x_4184_);
v___x_4188_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__0(v_declName_4183_, v_newTypes_4179_, v___x_4186_, v___x_4187_);
return v___x_4188_;
}
}
}
else
{
return v___x_4181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___lam__0___boxed(lean_object* v_newTypes_4189_, lean_object* v___x_4190_, lean_object* v___x_4191_, lean_object* v_x_4192_){
_start:
{
uint8_t v___x_7139__boxed_4193_; uint8_t v_res_4194_; lean_object* v_r_4195_; 
v___x_7139__boxed_4193_ = lean_unbox(v___x_4191_);
v_res_4194_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___lam__0(v_newTypes_4189_, v___x_4190_, v___x_7139__boxed_4193_, v_x_4192_);
lean_dec_ref(v_x_4192_);
lean_dec(v___x_4190_);
lean_dec_ref(v_newTypes_4189_);
v_r_4195_ = lean_box(v_res_4194_);
return v_r_4195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg(lean_object* v___x_4196_, uint8_t v_looseBVars_4197_, lean_object* v_range_4198_, lean_object* v_b_4199_, lean_object* v_i_4200_, lean_object* v___y_4201_){
_start:
{
lean_object* v_stop_4202_; lean_object* v_step_4203_; lean_object* v_a_4205_; lean_object* v_snd_4206_; uint8_t v___x_4209_; 
v_stop_4202_ = lean_ctor_get(v_range_4198_, 1);
v_step_4203_ = lean_ctor_get(v_range_4198_, 2);
v___x_4209_ = lean_nat_dec_lt(v_i_4200_, v_stop_4202_);
if (v___x_4209_ == 0)
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
lean_dec(v_i_4200_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v_b_4199_);
lean_ctor_set(v___x_4210_, 1, v___y_4201_);
v___x_4211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4210_);
return v___x_4211_;
}
else
{
lean_object* v_fst_4212_; lean_object* v_snd_4213_; lean_object* v___x_4215_; uint8_t v_isShared_4216_; uint8_t v_isSharedCheck_4241_; 
v_fst_4212_ = lean_ctor_get(v_b_4199_, 0);
v_snd_4213_ = lean_ctor_get(v_b_4199_, 1);
v_isSharedCheck_4241_ = !lean_is_exclusive(v_b_4199_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4215_ = v_b_4199_;
v_isShared_4216_ = v_isSharedCheck_4241_;
goto v_resetjp_4214_;
}
else
{
lean_inc(v_snd_4213_);
lean_inc(v_fst_4212_);
lean_dec(v_b_4199_);
v___x_4215_ = lean_box(0);
v_isShared_4216_ = v_isSharedCheck_4241_;
goto v_resetjp_4214_;
}
v_resetjp_4214_:
{
lean_object* v___x_4217_; uint8_t v___x_4218_; uint8_t v_looseBVars_4220_; lean_object* v___y_4221_; lean_object* v___x_4237_; lean_object* v___x_4238_; uint8_t v___x_4239_; 
v___x_4217_ = lean_unsigned_to_nat(0u);
v___x_4218_ = 0;
v___x_4237_ = l_Lean_instInhabitedExpr;
v___x_4238_ = lean_array_get_borrowed(v___x_4237_, v___x_4196_, v_i_4200_);
v___x_4239_ = l_Lean_Expr_hasLooseBVars(v___x_4238_);
if (v___x_4239_ == 0)
{
uint8_t v___x_4240_; 
v___x_4240_ = lean_unbox(v_snd_4213_);
lean_dec(v_snd_4213_);
v_looseBVars_4220_ = v___x_4240_;
v___y_4221_ = v___y_4201_;
goto v___jp_4219_;
}
else
{
lean_dec(v_snd_4213_);
v_looseBVars_4220_ = v_looseBVars_4197_;
v___y_4221_ = v___y_4201_;
goto v___jp_4219_;
}
v___jp_4219_:
{
lean_object* v_newTypes_4222_; lean_object* v___x_4223_; lean_object* v___f_4224_; lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v_newTypes_4222_ = lean_ctor_get(v___y_4221_, 3);
v___x_4223_ = lean_box(v___x_4218_);
lean_inc_ref(v_newTypes_4222_);
v___f_4224_ = lean_alloc_closure((void*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_4224_, 0, v_newTypes_4222_);
lean_closure_set(v___f_4224_, 1, v___x_4217_);
lean_closure_set(v___f_4224_, 2, v___x_4223_);
v___x_4225_ = l_Lean_instInhabitedExpr;
v___x_4226_ = lean_array_get_borrowed(v___x_4225_, v___x_4196_, v_i_4200_);
v___x_4227_ = lean_find_expr(v___f_4224_, v___x_4226_);
lean_dec_ref(v___f_4224_);
if (lean_obj_tag(v___x_4227_) == 1)
{
lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4231_; 
lean_dec_ref(v___x_4227_);
lean_dec(v_fst_4212_);
v___x_4228_ = lean_box(v_looseBVars_4197_);
v___x_4229_ = lean_box(v_looseBVars_4220_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 1, v___x_4229_);
lean_ctor_set(v___x_4215_, 0, v___x_4228_);
v___x_4231_ = v___x_4215_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v___x_4228_);
lean_ctor_set(v_reuseFailAlloc_4232_, 1, v___x_4229_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
v_a_4205_ = v___x_4231_;
v_snd_4206_ = v___y_4221_;
goto v___jp_4204_;
}
}
else
{
lean_object* v___x_4233_; lean_object* v___x_4235_; 
lean_dec(v___x_4227_);
v___x_4233_ = lean_box(v_looseBVars_4220_);
if (v_isShared_4216_ == 0)
{
lean_ctor_set(v___x_4215_, 1, v___x_4233_);
v___x_4235_ = v___x_4215_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_fst_4212_);
lean_ctor_set(v_reuseFailAlloc_4236_, 1, v___x_4233_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
v_a_4205_ = v___x_4235_;
v_snd_4206_ = v___y_4221_;
goto v___jp_4204_;
}
}
}
}
}
v___jp_4204_:
{
lean_object* v___x_4207_; 
v___x_4207_ = lean_nat_add(v_i_4200_, v_step_4203_);
lean_dec(v_i_4200_);
v_b_4199_ = v_a_4205_;
v_i_4200_ = v___x_4207_;
v___y_4201_ = v_snd_4206_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg___boxed(lean_object* v___x_4242_, lean_object* v_looseBVars_4243_, lean_object* v_range_4244_, lean_object* v_b_4245_, lean_object* v_i_4246_, lean_object* v___y_4247_){
_start:
{
uint8_t v_looseBVars_boxed_4248_; lean_object* v_res_4249_; 
v_looseBVars_boxed_4248_ = lean_unbox(v_looseBVars_4243_);
v_res_4249_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg(v___x_4242_, v_looseBVars_boxed_4248_, v_range_4244_, v_b_4245_, v_i_4246_, v___y_4247_);
lean_dec_ref(v_range_4244_);
lean_dec_ref(v___x_4242_);
return v_res_4249_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f(lean_object* v_e_4255_, lean_object* v_a_4256_, lean_object* v_a_4257_){
_start:
{
lean_object* v___y_4259_; uint8_t v_looseBVars_4263_; 
v_looseBVars_4263_ = l_Lean_Expr_isApp(v_e_4255_);
if (v_looseBVars_4263_ == 0)
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
lean_dec_ref(v_e_4255_);
v___x_4264_ = lean_box(0);
v___x_4265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4264_);
lean_ctor_set(v___x_4265_, 1, v_a_4257_);
v___x_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4266_, 0, v___x_4265_);
return v___x_4266_;
}
else
{
lean_object* v___x_4267_; 
v___x_4267_ = l_Lean_Expr_getAppFn(v_e_4255_);
if (lean_obj_tag(v___x_4267_) == 4)
{
lean_object* v_declName_4268_; lean_object* v___x_4269_; 
v_declName_4268_ = lean_ctor_get(v___x_4267_, 0);
lean_inc(v_declName_4268_);
lean_dec_ref(v___x_4267_);
lean_inc_ref(v_a_4256_);
v___x_4269_ = lean_environment_find(v_a_4256_, v_declName_4268_);
if (lean_obj_tag(v___x_4269_) == 1)
{
lean_object* v_val_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4339_; 
v_val_4270_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4272_ = v___x_4269_;
v_isShared_4273_ = v_isSharedCheck_4339_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_val_4270_);
lean_dec(v___x_4269_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4339_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
if (lean_obj_tag(v_val_4270_) == 5)
{
lean_object* v_val_4274_; lean_object* v___x_4276_; uint8_t v_isShared_4277_; uint8_t v_isSharedCheck_4338_; 
v_val_4274_ = lean_ctor_get(v_val_4270_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v_val_4270_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4276_ = v_val_4270_;
v_isShared_4277_ = v_isSharedCheck_4338_;
goto v_resetjp_4275_;
}
else
{
lean_inc(v_val_4274_);
lean_dec(v_val_4270_);
v___x_4276_ = lean_box(0);
v_isShared_4277_ = v_isSharedCheck_4338_;
goto v_resetjp_4275_;
}
v_resetjp_4275_:
{
lean_object* v_numParams_4278_; lean_object* v_nargs_4279_; lean_object* v_dummy_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; uint8_t v___x_4286_; 
v_numParams_4278_ = lean_ctor_get(v_val_4274_, 1);
v_nargs_4279_ = l_Lean_Expr_getAppNumArgs(v_e_4255_);
v_dummy_4280_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
lean_inc(v_nargs_4279_);
v___x_4281_ = lean_mk_array(v_nargs_4279_, v_dummy_4280_);
v___x_4282_ = lean_unsigned_to_nat(1u);
v___x_4283_ = lean_nat_sub(v_nargs_4279_, v___x_4282_);
lean_dec(v_nargs_4279_);
v___x_4284_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_4255_, v___x_4281_, v___x_4283_);
v___x_4285_ = lean_array_get_size(v___x_4284_);
v___x_4286_ = lean_nat_dec_lt(v___x_4285_, v_numParams_4278_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4332_; 
lean_del_object(v___x_4276_);
v___x_4287_ = lean_unsigned_to_nat(0u);
lean_inc(v_numParams_4278_);
v___x_4288_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4287_);
lean_ctor_set(v___x_4288_, 1, v_numParams_4278_);
lean_ctor_set(v___x_4288_, 2, v___x_4282_);
v___x_4289_ = lean_box(v___x_4286_);
v___x_4290_ = lean_box(v___x_4286_);
v___x_4291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4291_, 0, v___x_4289_);
lean_ctor_set(v___x_4291_, 1, v___x_4290_);
v___x_4292_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg(v___x_4284_, v_looseBVars_4263_, v___x_4288_, v___x_4291_, v___x_4287_, v_a_4257_);
lean_dec_ref(v___x_4288_);
lean_dec_ref(v___x_4284_);
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4295_ = v___x_4292_;
v_isShared_4296_ = v_isSharedCheck_4332_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4332_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v_fst_4297_; lean_object* v_fst_4298_; uint8_t v___x_4299_; 
v_fst_4297_ = lean_ctor_get(v_a_4293_, 0);
lean_inc(v_fst_4297_);
v_fst_4298_ = lean_ctor_get(v_fst_4297_, 0);
v___x_4299_ = lean_unbox(v_fst_4298_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4301_; uint8_t v_isShared_4302_; uint8_t v_isSharedCheck_4311_; 
lean_dec_ref(v_val_4274_);
lean_del_object(v___x_4272_);
v_isSharedCheck_4311_ = !lean_is_exclusive(v_fst_4297_);
if (v_isSharedCheck_4311_ == 0)
{
lean_object* v_unused_4312_; lean_object* v_unused_4313_; 
v_unused_4312_ = lean_ctor_get(v_fst_4297_, 1);
lean_dec(v_unused_4312_);
v_unused_4313_ = lean_ctor_get(v_fst_4297_, 0);
lean_dec(v_unused_4313_);
v___x_4301_ = v_fst_4297_;
v_isShared_4302_ = v_isSharedCheck_4311_;
goto v_resetjp_4300_;
}
else
{
lean_dec(v_fst_4297_);
v___x_4301_ = lean_box(0);
v_isShared_4302_ = v_isSharedCheck_4311_;
goto v_resetjp_4300_;
}
v_resetjp_4300_:
{
lean_object* v_snd_4303_; lean_object* v___x_4304_; lean_object* v___x_4306_; 
v_snd_4303_ = lean_ctor_get(v_a_4293_, 1);
lean_inc(v_snd_4303_);
lean_dec(v_a_4293_);
v___x_4304_ = lean_box(0);
if (v_isShared_4302_ == 0)
{
lean_ctor_set(v___x_4301_, 1, v_snd_4303_);
lean_ctor_set(v___x_4301_, 0, v___x_4304_);
v___x_4306_ = v___x_4301_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4304_);
lean_ctor_set(v_reuseFailAlloc_4310_, 1, v_snd_4303_);
v___x_4306_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4308_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4306_);
v___x_4308_ = v___x_4295_;
goto v_reusejp_4307_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4306_);
v___x_4308_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4307_;
}
v_reusejp_4307_:
{
return v___x_4308_;
}
}
}
}
else
{
lean_object* v_snd_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4330_; 
v_snd_4314_ = lean_ctor_get(v_fst_4297_, 1);
v_isSharedCheck_4330_ = !lean_is_exclusive(v_fst_4297_);
if (v_isSharedCheck_4330_ == 0)
{
lean_object* v_unused_4331_; 
v_unused_4331_ = lean_ctor_get(v_fst_4297_, 0);
lean_dec(v_unused_4331_);
v___x_4316_ = v_fst_4297_;
v_isShared_4317_ = v_isSharedCheck_4330_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_snd_4314_);
lean_dec(v_fst_4297_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4330_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
uint8_t v___x_4318_; 
v___x_4318_ = lean_unbox(v_snd_4314_);
lean_dec(v_snd_4314_);
if (v___x_4318_ == 0)
{
lean_object* v_snd_4319_; lean_object* v___x_4321_; 
v_snd_4319_ = lean_ctor_get(v_a_4293_, 1);
lean_inc(v_snd_4319_);
lean_dec(v_a_4293_);
if (v_isShared_4273_ == 0)
{
lean_ctor_set(v___x_4272_, 0, v_val_4274_);
v___x_4321_ = v___x_4272_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_val_4274_);
v___x_4321_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
lean_object* v___x_4323_; 
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 1, v_snd_4319_);
lean_ctor_set(v___x_4316_, 0, v___x_4321_);
v___x_4323_ = v___x_4316_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4321_);
lean_ctor_set(v_reuseFailAlloc_4327_, 1, v_snd_4319_);
v___x_4323_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4325_; 
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4323_);
v___x_4325_ = v___x_4295_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v___x_4323_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
return v___x_4325_;
}
}
}
}
else
{
lean_object* v___x_4329_; 
lean_del_object(v___x_4316_);
lean_del_object(v___x_4295_);
lean_dec(v_a_4293_);
lean_dec_ref(v_val_4274_);
lean_del_object(v___x_4272_);
v___x_4329_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___closed__2));
return v___x_4329_;
}
}
}
}
}
else
{
lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
lean_dec_ref(v___x_4284_);
lean_dec_ref(v_val_4274_);
lean_del_object(v___x_4272_);
v___x_4333_ = lean_box(0);
v___x_4334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
lean_ctor_set(v___x_4334_, 1, v_a_4257_);
if (v_isShared_4277_ == 0)
{
lean_ctor_set_tag(v___x_4276_, 1);
lean_ctor_set(v___x_4276_, 0, v___x_4334_);
v___x_4336_ = v___x_4276_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
else
{
lean_del_object(v___x_4272_);
lean_dec(v_val_4270_);
lean_dec_ref(v_e_4255_);
v___y_4259_ = v_a_4257_;
goto v___jp_4258_;
}
}
}
else
{
lean_dec(v___x_4269_);
lean_dec_ref(v_e_4255_);
v___y_4259_ = v_a_4257_;
goto v___jp_4258_;
}
}
else
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
lean_dec_ref(v___x_4267_);
lean_dec_ref(v_e_4255_);
v___x_4340_ = lean_box(0);
v___x_4341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
lean_ctor_set(v___x_4341_, 1, v_a_4257_);
v___x_4342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4342_, 0, v___x_4341_);
return v___x_4342_;
}
}
v___jp_4258_:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v___x_4260_ = lean_box(0);
v___x_4261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
lean_ctor_set(v___x_4261_, 1, v___y_4259_);
v___x_4262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4261_);
return v___x_4262_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f___boxed(lean_object* v_e_4343_, lean_object* v_a_4344_, lean_object* v_a_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f(v_e_4343_, v_a_4344_, v_a_4345_);
lean_dec_ref(v_a_4344_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1(lean_object* v___x_4347_, uint8_t v_looseBVars_4348_, lean_object* v_range_4349_, lean_object* v_b_4350_, lean_object* v_i_4351_, lean_object* v_hs_4352_, lean_object* v_hl_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v___x_4356_; 
v___x_4356_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___redArg(v___x_4347_, v_looseBVars_4348_, v_range_4349_, v_b_4350_, v_i_4351_, v___y_4355_);
return v___x_4356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1___boxed(lean_object* v___x_4357_, lean_object* v_looseBVars_4358_, lean_object* v_range_4359_, lean_object* v_b_4360_, lean_object* v_i_4361_, lean_object* v_hs_4362_, lean_object* v_hl_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
uint8_t v_looseBVars_boxed_4366_; lean_object* v_res_4367_; 
v_looseBVars_boxed_4366_ = lean_unbox(v_looseBVars_4358_);
v_res_4367_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f_spec__1(v___x_4357_, v_looseBVars_boxed_4366_, v_range_4359_, v_b_4360_, v_i_4361_, v_hs_4362_, v_hl_4363_, v___y_4364_, v___y_4365_);
lean_dec_ref(v___y_4364_);
lean_dec_ref(v_range_4359_);
lean_dec_ref(v___x_4357_);
return v_res_4367_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg(lean_object* v_range_4370_, lean_object* v_b_4371_, lean_object* v_i_4372_){
_start:
{
lean_object* v_stop_4373_; lean_object* v_step_4374_; uint8_t v___x_4375_; 
v_stop_4373_ = lean_ctor_get(v_range_4370_, 1);
v_step_4374_ = lean_ctor_get(v_range_4370_, 2);
v___x_4375_ = lean_nat_dec_lt(v_i_4372_, v_stop_4373_);
if (v___x_4375_ == 0)
{
lean_object* v___x_4376_; 
lean_dec(v_i_4372_);
v___x_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4376_, 0, v_b_4371_);
return v___x_4376_;
}
else
{
if (lean_obj_tag(v_b_4371_) == 7)
{
lean_object* v_body_4377_; lean_object* v___x_4378_; 
v_body_4377_ = lean_ctor_get(v_b_4371_, 2);
lean_inc_ref(v_body_4377_);
lean_dec_ref(v_b_4371_);
v___x_4378_ = lean_nat_add(v_i_4372_, v_step_4374_);
lean_dec(v_i_4372_);
v_b_4371_ = v_body_4377_;
v_i_4372_ = v___x_4378_;
goto _start;
}
else
{
lean_object* v___x_4380_; 
lean_dec(v_i_4372_);
lean_dec_ref(v_b_4371_);
v___x_4380_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg___closed__0));
return v___x_4380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg___boxed(lean_object* v_range_4381_, lean_object* v_b_4382_, lean_object* v_i_4383_){
_start:
{
lean_object* v_res_4384_; 
v_res_4384_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg(v_range_4381_, v_b_4382_, v_i_4383_);
lean_dec_ref(v_range_4381_);
return v_res_4384_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instantiateForallParams(lean_object* v_e_4385_, lean_object* v_hi_4386_, lean_object* v_params_4387_){
_start:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
v___x_4388_ = lean_unsigned_to_nat(0u);
v___x_4389_ = lean_unsigned_to_nat(1u);
lean_inc(v_hi_4386_);
v___x_4390_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4388_);
lean_ctor_set(v___x_4390_, 1, v_hi_4386_);
lean_ctor_set(v___x_4390_, 2, v___x_4389_);
v___x_4391_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg(v___x_4390_, v_e_4385_, v___x_4388_);
lean_dec_ref(v___x_4390_);
if (lean_obj_tag(v___x_4391_) == 0)
{
lean_dec(v_hi_4386_);
return v___x_4391_;
}
else
{
lean_object* v_a_4392_; lean_object* v___x_4394_; uint8_t v_isShared_4395_; uint8_t v_isSharedCheck_4400_; 
v_a_4392_ = lean_ctor_get(v___x_4391_, 0);
v_isSharedCheck_4400_ = !lean_is_exclusive(v___x_4391_);
if (v_isSharedCheck_4400_ == 0)
{
v___x_4394_ = v___x_4391_;
v_isShared_4395_ = v_isSharedCheck_4400_;
goto v_resetjp_4393_;
}
else
{
lean_inc(v_a_4392_);
lean_dec(v___x_4391_);
v___x_4394_ = lean_box(0);
v_isShared_4395_ = v_isSharedCheck_4400_;
goto v_resetjp_4393_;
}
v_resetjp_4393_:
{
lean_object* v___x_4396_; lean_object* v___x_4398_; 
v___x_4396_ = lean_expr_instantiate_rev_range(v_a_4392_, v___x_4388_, v_hi_4386_, v_params_4387_);
lean_dec(v_hi_4386_);
lean_dec(v_a_4392_);
if (v_isShared_4395_ == 0)
{
lean_ctor_set(v___x_4394_, 0, v___x_4396_);
v___x_4398_ = v___x_4394_;
goto v_reusejp_4397_;
}
else
{
lean_object* v_reuseFailAlloc_4399_; 
v_reuseFailAlloc_4399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4399_, 0, v___x_4396_);
v___x_4398_ = v_reuseFailAlloc_4399_;
goto v_reusejp_4397_;
}
v_reusejp_4397_:
{
return v___x_4398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_instantiateForallParams___boxed(lean_object* v_e_4401_, lean_object* v_hi_4402_, lean_object* v_params_4403_){
_start:
{
lean_object* v_res_4404_; 
v_res_4404_ = l_Lean4Lean_ElimNestedInductive_instantiateForallParams(v_e_4401_, v_hi_4402_, v_params_4403_);
lean_dec_ref(v_params_4403_);
return v_res_4404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0(lean_object* v_range_4405_, lean_object* v_b_4406_, lean_object* v_i_4407_, lean_object* v_hs_4408_, lean_object* v_hl_4409_){
_start:
{
lean_object* v___x_4410_; 
v___x_4410_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___redArg(v_range_4405_, v_b_4406_, v_i_4407_);
return v___x_4410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0___boxed(lean_object* v_range_4411_, lean_object* v_b_4412_, lean_object* v_i_4413_, lean_object* v_hs_4414_, lean_object* v_hl_4415_){
_start:
{
lean_object* v_res_4416_; 
v_res_4416_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_instantiateForallParams_spec__0(v_range_4411_, v_b_4412_, v_i_4413_, v_hs_4414_, v_hl_4415_);
lean_dec_ref(v_range_4411_);
return v_res_4416_;
}
}
static lean_object* _init_l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___closed__0(void){
_start:
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4417_ = lean_box(0);
v___x_4418_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12));
v___x_4419_ = l_instInhabitedOfMonad___redArg(v___x_4418_, v___x_4417_);
return v___x_4419_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0(lean_object* v_msg_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v___x_4423_; lean_object* v___f_4424_; lean_object* v___x_19108__overap_4425_; lean_object* v___x_4426_; 
v___x_4423_ = lean_obj_once(&l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___closed__0, &l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___closed__0_once, _init_l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___closed__0);
v___f_4424_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4424_, 0, v___x_4423_);
v___x_19108__overap_4425_ = lean_panic_fn_borrowed(v___f_4424_, v_msg_4420_);
lean_dec_ref(v___f_4424_);
lean_inc_ref(v___y_4421_);
v___x_4426_ = lean_apply_2(v___x_19108__overap_4425_, v___y_4421_, v___y_4422_);
return v___x_4426_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0___boxed(lean_object* v_msg_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_){
_start:
{
lean_object* v_res_4430_; 
v_res_4430_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0(v_msg_4427_, v___y_4428_, v___y_4429_);
lean_dec_ref(v___y_4428_);
return v_res_4430_;
}
}
static lean_object* _init_l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___closed__0(void){
_start:
{
lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; 
v___x_4431_ = lean_box(0);
v___x_4432_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12));
v___x_4433_ = l_instInhabitedOfMonad___redArg(v___x_4432_, v___x_4431_);
return v___x_4433_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2(lean_object* v_msg_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4437_; lean_object* v___f_4438_; lean_object* v___x_19586__overap_4439_; lean_object* v___x_4440_; 
v___x_4437_ = lean_obj_once(&l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___closed__0, &l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___closed__0_once, _init_l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___closed__0);
v___f_4438_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_4438_, 0, v___x_4437_);
v___x_19586__overap_4439_ = lean_panic_fn_borrowed(v___f_4438_, v_msg_4434_);
lean_dec_ref(v___f_4438_);
lean_inc_ref(v___y_4435_);
v___x_4440_ = lean_apply_2(v___x_19586__overap_4439_, v___y_4435_, v___y_4436_);
return v___x_4440_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2___boxed(lean_object* v_msg_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v_res_4444_; 
v_res_4444_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2(v_msg_4441_, v___y_4442_, v___y_4443_);
lean_dec_ref(v___y_4442_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___redArg(lean_object* v___y_4445_, lean_object* v_us_4446_, lean_object* v___x_4447_, lean_object* v_args_4448_, lean_object* v_a_4449_, lean_object* v_fst_4450_, lean_object* v_lctx_4451_, lean_object* v_As_4452_, lean_object* v_x_4453_, lean_object* v_x_4454_, lean_object* v___y_4455_){
_start:
{
if (lean_obj_tag(v_x_4453_) == 0)
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; 
lean_dec_ref(v_lctx_4451_);
lean_dec(v___x_4447_);
lean_dec(v_us_4446_);
v___x_4456_ = l_List_reverse___redArg(v_x_4454_);
v___x_4457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4457_, 0, v___x_4456_);
lean_ctor_set(v___x_4457_, 1, v___y_4455_);
v___x_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
return v___x_4458_;
}
else
{
lean_object* v_head_4459_; lean_object* v_tail_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4496_; 
v_head_4459_ = lean_ctor_get(v_x_4453_, 0);
v_tail_4460_ = lean_ctor_get(v_x_4453_, 1);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_x_4453_);
if (v_isSharedCheck_4496_ == 0)
{
v___x_4462_ = v_x_4453_;
v_isShared_4463_ = v_isSharedCheck_4496_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_tail_4460_);
lean_inc(v_head_4459_);
lean_dec(v_x_4453_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4496_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4464_; 
lean_inc(v_head_4459_);
lean_inc_ref(v___y_4445_);
v___x_4464_ = l_Lean_Kernel_Environment_get(v___y_4445_, v_head_4459_);
if (lean_obj_tag(v___x_4464_) == 0)
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
lean_del_object(v___x_4462_);
lean_dec(v_tail_4460_);
lean_dec(v_head_4459_);
lean_dec_ref(v___y_4455_);
lean_dec(v_x_4454_);
lean_dec_ref(v_lctx_4451_);
lean_dec(v___x_4447_);
lean_dec(v_us_4446_);
v_a_4465_ = lean_ctor_get(v___x_4464_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___x_4464_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___x_4464_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
return v___x_4470_;
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; 
v_a_4473_ = lean_ctor_get(v___x_4464_, 0);
lean_inc(v_a_4473_);
lean_dec_ref(v___x_4464_);
v___x_4474_ = l_Lean_ConstantInfo_type(v_a_4473_);
v___x_4475_ = l_Lean_ConstantInfo_levelParams(v_a_4473_);
lean_dec(v_a_4473_);
lean_inc(v_us_4446_);
v___x_4476_ = l_Lean_Expr_instantiateLevelParams(v___x_4474_, v___x_4475_, v_us_4446_);
lean_dec_ref(v___x_4474_);
lean_inc(v___x_4447_);
v___x_4477_ = l_Lean4Lean_ElimNestedInductive_instantiateForallParams(v___x_4476_, v___x_4447_, v_args_4448_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_del_object(v___x_4462_);
lean_dec(v_tail_4460_);
lean_dec(v_head_4459_);
lean_dec_ref(v___y_4455_);
lean_dec(v_x_4454_);
lean_dec_ref(v_lctx_4451_);
lean_dec(v___x_4447_);
lean_dec(v_us_4446_);
v_a_4478_ = lean_ctor_get(v___x_4477_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4477_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4477_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4477_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
else
{
lean_object* v_a_4486_; uint8_t v___x_4487_; uint8_t v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4493_; 
v_a_4486_ = lean_ctor_get(v___x_4477_, 0);
lean_inc(v_a_4486_);
lean_dec_ref(v___x_4477_);
v___x_4487_ = 1;
v___x_4488_ = 0;
v___x_4489_ = l_Lean_Name_replacePrefix(v_head_4459_, v_a_4449_, v_fst_4450_);
lean_inc_ref(v_lctx_4451_);
v___x_4490_ = l_Lean_LocalContext_mkForall(v_lctx_4451_, v_As_4452_, v_a_4486_, v___x_4487_, v___x_4488_);
lean_dec(v_a_4486_);
v___x_4491_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4491_, 0, v___x_4489_);
lean_ctor_set(v___x_4491_, 1, v___x_4490_);
if (v_isShared_4463_ == 0)
{
lean_ctor_set(v___x_4462_, 1, v_x_4454_);
lean_ctor_set(v___x_4462_, 0, v___x_4491_);
v___x_4493_ = v___x_4462_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4495_; 
v_reuseFailAlloc_4495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4495_, 0, v___x_4491_);
lean_ctor_set(v_reuseFailAlloc_4495_, 1, v_x_4454_);
v___x_4493_ = v_reuseFailAlloc_4495_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
v_x_4453_ = v_tail_4460_;
v_x_4454_ = v___x_4493_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___redArg___boxed(lean_object* v___y_4497_, lean_object* v_us_4498_, lean_object* v___x_4499_, lean_object* v_args_4500_, lean_object* v_a_4501_, lean_object* v_fst_4502_, lean_object* v_lctx_4503_, lean_object* v_As_4504_, lean_object* v_x_4505_, lean_object* v_x_4506_, lean_object* v___y_4507_){
_start:
{
lean_object* v_res_4508_; 
v_res_4508_ = l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___redArg(v___y_4497_, v_us_4498_, v___x_4499_, v_args_4500_, v_a_4501_, v_fst_4502_, v_lctx_4503_, v_As_4504_, v_x_4505_, v_x_4506_, v___y_4507_);
lean_dec_ref(v_As_4504_);
lean_dec(v_fst_4502_);
lean_dec(v_a_4501_);
lean_dec_ref(v_args_4500_);
lean_dec_ref(v___y_4497_);
return v_res_4508_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v___x_4513_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_4514_ = lean_unsigned_to_nat(46u);
v___x_4515_ = lean_unsigned_to_nat(642u);
v___x_4516_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__2));
v___x_4517_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_4518_ = l_mkPanicMessageWithDecl(v___x_4517_, v___x_4516_, v___x_4515_, v___x_4514_, v___x_4513_);
return v___x_4518_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg(lean_object* v___y_4519_, lean_object* v_us_4520_, lean_object* v___x_4521_, lean_object* v_args_4522_, lean_object* v_params_4523_, lean_object* v_As_4524_, lean_object* v_lctx_4525_, lean_object* v_declName_4526_, lean_object* v___x_4527_, lean_object* v_as_x27_4528_, lean_object* v_b_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
if (lean_obj_tag(v_as_x27_4528_) == 0)
{
lean_object* v___x_4532_; lean_object* v___x_4533_; 
lean_dec_ref(v_lctx_4525_);
lean_dec(v___x_4521_);
lean_dec(v_us_4520_);
v___x_4532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4532_, 0, v_b_4529_);
lean_ctor_set(v___x_4532_, 1, v___y_4531_);
v___x_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
return v___x_4533_;
}
else
{
lean_object* v_head_4534_; lean_object* v_tail_4535_; lean_object* v___x_4536_; 
v_head_4534_ = lean_ctor_get(v_as_x27_4528_, 0);
v_tail_4535_ = lean_ctor_get(v_as_x27_4528_, 1);
lean_inc(v_head_4534_);
lean_inc_ref(v___y_4519_);
v___x_4536_ = l_Lean_Kernel_Environment_get(v___y_4519_, v_head_4534_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_dec_ref(v___y_4531_);
lean_dec(v_b_4529_);
lean_dec_ref(v_lctx_4525_);
lean_dec(v___x_4521_);
lean_dec(v_us_4520_);
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4536_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4536_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
else
{
lean_object* v_a_4545_; 
v_a_4545_ = lean_ctor_get(v___x_4536_, 0);
lean_inc(v_a_4545_);
lean_dec_ref(v___x_4536_);
if (lean_obj_tag(v_a_4545_) == 5)
{
lean_object* v_val_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4663_; 
v_val_4546_ = lean_ctor_get(v_a_4545_, 0);
v_isSharedCheck_4663_ = !lean_is_exclusive(v_a_4545_);
if (v_isSharedCheck_4663_ == 0)
{
v___x_4548_ = v_a_4545_;
v_isShared_4549_ = v_isSharedCheck_4663_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_val_4546_);
lean_dec(v_a_4545_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4663_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_inc(v_us_4520_);
lean_inc_n(v_head_4534_, 2);
v___x_4550_ = l_Lean_Expr_const___override(v_head_4534_, v_us_4520_);
v___x_4551_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__1));
v___x_4552_ = l_Lean_Name_append(v___x_4551_, v_head_4534_);
v___x_4553_ = l_Lean4Lean_ElimNestedInductive_mkUniqueName(v___x_4552_, v___y_4530_, v___y_4531_);
if (lean_obj_tag(v___x_4553_) == 0)
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec_ref(v___x_4550_);
lean_del_object(v___x_4548_);
lean_dec_ref(v_val_4546_);
lean_dec(v_b_4529_);
lean_dec_ref(v_lctx_4525_);
lean_dec(v___x_4521_);
lean_dec(v_us_4520_);
v_a_4554_ = lean_ctor_get(v___x_4553_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4553_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4553_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4553_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
else
{
lean_object* v_a_4562_; lean_object* v_toConstantVal_4563_; lean_object* v_fst_4564_; lean_object* v_snd_4565_; lean_object* v_ctors_4566_; lean_object* v_levelParams_4567_; lean_object* v_type_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4661_; 
v_a_4562_ = lean_ctor_get(v___x_4553_, 0);
lean_inc(v_a_4562_);
lean_dec_ref(v___x_4553_);
v_toConstantVal_4563_ = lean_ctor_get(v_val_4546_, 0);
lean_inc_ref(v_toConstantVal_4563_);
v_fst_4564_ = lean_ctor_get(v_a_4562_, 0);
lean_inc(v_fst_4564_);
v_snd_4565_ = lean_ctor_get(v_a_4562_, 1);
lean_inc(v_snd_4565_);
lean_dec(v_a_4562_);
v_ctors_4566_ = lean_ctor_get(v_val_4546_, 4);
lean_inc(v_ctors_4566_);
lean_dec_ref(v_val_4546_);
v_levelParams_4567_ = lean_ctor_get(v_toConstantVal_4563_, 1);
v_type_4568_ = lean_ctor_get(v_toConstantVal_4563_, 2);
v_isSharedCheck_4661_ = !lean_is_exclusive(v_toConstantVal_4563_);
if (v_isSharedCheck_4661_ == 0)
{
lean_object* v_unused_4662_; 
v_unused_4662_ = lean_ctor_get(v_toConstantVal_4563_, 0);
lean_dec(v_unused_4662_);
v___x_4570_ = v_toConstantVal_4563_;
v_isShared_4571_ = v_isSharedCheck_4661_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_type_4568_);
lean_inc(v_levelParams_4567_);
lean_dec(v_toConstantVal_4563_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4661_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; 
v___x_4572_ = lean_unsigned_to_nat(0u);
v___x_4573_ = l_Lean_mkAppRange(v___x_4550_, v___x_4572_, v___x_4521_, v_args_4522_);
lean_inc(v_us_4520_);
v___x_4574_ = l_Lean_Expr_instantiateLevelParams(v_type_4568_, v_levelParams_4567_, v_us_4520_);
lean_dec_ref(v_type_4568_);
lean_inc(v___x_4521_);
v___x_4575_ = l_Lean4Lean_ElimNestedInductive_instantiateForallParams(v___x_4574_, v___x_4521_, v_args_4522_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v_a_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4583_; 
lean_dec_ref(v___x_4573_);
lean_del_object(v___x_4570_);
lean_dec(v_ctors_4566_);
lean_dec(v_snd_4565_);
lean_dec(v_fst_4564_);
lean_del_object(v___x_4548_);
lean_dec(v_b_4529_);
lean_dec_ref(v_lctx_4525_);
lean_dec(v___x_4521_);
lean_dec(v_us_4520_);
v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4583_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4583_ == 0)
{
v___x_4578_ = v___x_4575_;
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_a_4576_);
lean_dec(v___x_4575_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4583_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4581_; 
if (v_isShared_4579_ == 0)
{
v___x_4581_ = v___x_4578_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4582_; 
v_reuseFailAlloc_4582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
v___x_4581_ = v_reuseFailAlloc_4582_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
return v___x_4581_;
}
}
}
else
{
lean_object* v_a_4584_; lean_object* v___x_4585_; 
v_a_4584_ = lean_ctor_get(v___x_4575_, 0);
lean_inc(v_a_4584_);
lean_dec_ref(v___x_4575_);
v___x_4585_ = l_Lean4Lean_ElimNestedInductive_replaceParams(v_params_4523_, v___x_4573_, v_As_4524_, v___y_4530_, v_snd_4565_);
lean_dec_ref(v___x_4573_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4593_; 
lean_dec(v_a_4584_);
lean_del_object(v___x_4570_);
lean_dec(v_ctors_4566_);
lean_dec(v_fst_4564_);
lean_del_object(v___x_4548_);
lean_dec(v_b_4529_);
lean_dec_ref(v_lctx_4525_);
lean_dec(v___x_4521_);
lean_dec(v_us_4520_);
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4593_ == 0)
{
v___x_4588_ = v___x_4585_;
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4585_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4593_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4591_; 
if (v_isShared_4589_ == 0)
{
v___x_4591_ = v___x_4588_;
goto v_reusejp_4590_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v_a_4586_);
v___x_4591_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4590_;
}
v_reusejp_4590_:
{
return v___x_4591_;
}
}
}
else
{
lean_object* v_a_4594_; lean_object* v_snd_4595_; lean_object* v_fst_4596_; lean_object* v___x_4598_; uint8_t v_isShared_4599_; uint8_t v_isSharedCheck_4660_; 
v_a_4594_ = lean_ctor_get(v___x_4585_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4585_);
v_snd_4595_ = lean_ctor_get(v_a_4594_, 1);
v_fst_4596_ = lean_ctor_get(v_a_4594_, 0);
v_isSharedCheck_4660_ = !lean_is_exclusive(v_a_4594_);
if (v_isSharedCheck_4660_ == 0)
{
v___x_4598_ = v_a_4594_;
v_isShared_4599_ = v_isSharedCheck_4660_;
goto v_resetjp_4597_;
}
else
{
lean_inc(v_snd_4595_);
lean_inc(v_fst_4596_);
lean_dec(v_a_4594_);
v___x_4598_ = lean_box(0);
v_isShared_4599_ = v_isSharedCheck_4660_;
goto v_resetjp_4597_;
}
v_resetjp_4597_:
{
lean_object* v_ngen_4600_; lean_object* v_nestedAux_4601_; lean_object* v_lvls_4602_; lean_object* v_newTypes_4603_; lean_object* v_nextIdx_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4659_; 
v_ngen_4600_ = lean_ctor_get(v_snd_4595_, 0);
v_nestedAux_4601_ = lean_ctor_get(v_snd_4595_, 1);
v_lvls_4602_ = lean_ctor_get(v_snd_4595_, 2);
v_newTypes_4603_ = lean_ctor_get(v_snd_4595_, 3);
v_nextIdx_4604_ = lean_ctor_get(v_snd_4595_, 4);
v_isSharedCheck_4659_ = !lean_is_exclusive(v_snd_4595_);
if (v_isSharedCheck_4659_ == 0)
{
v___x_4606_ = v_snd_4595_;
v_isShared_4607_ = v_isSharedCheck_4659_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_nextIdx_4604_);
lean_inc(v_newTypes_4603_);
lean_inc(v_lvls_4602_);
lean_inc(v_nestedAux_4601_);
lean_inc(v_ngen_4600_);
lean_dec(v_snd_4595_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4659_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
uint8_t v___x_4608_; uint8_t v___x_4609_; lean_object* v___x_4610_; lean_object* v_result_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; lean_object* v___x_4646_; 
v___x_4608_ = 1;
v___x_4609_ = 0;
lean_inc_ref(v_lctx_4525_);
v___x_4610_ = l_Lean_LocalContext_mkForall(v_lctx_4525_, v_As_4524_, v_a_4584_, v___x_4608_, v___x_4609_);
lean_dec(v_a_4584_);
lean_inc(v_fst_4564_);
if (v_isShared_4599_ == 0)
{
lean_ctor_set(v___x_4598_, 1, v_fst_4564_);
v___x_4646_ = v___x_4598_;
goto v_reusejp_4645_;
}
else
{
lean_object* v_reuseFailAlloc_4658_; 
v_reuseFailAlloc_4658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4658_, 0, v_fst_4596_);
lean_ctor_set(v_reuseFailAlloc_4658_, 1, v_fst_4564_);
v___x_4646_ = v_reuseFailAlloc_4658_;
goto v_reusejp_4645_;
}
v___jp_4611_:
{
lean_object* v___x_4615_; lean_object* v___x_4616_; 
v___x_4615_ = lean_box(0);
lean_inc_ref(v_lctx_4525_);
lean_inc(v___x_4521_);
lean_inc(v_us_4520_);
v___x_4616_ = l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___redArg(v___y_4519_, v_us_4520_, v___x_4521_, v_args_4522_, v_head_4534_, v_fst_4564_, v_lctx_4525_, v_As_4524_, v_ctors_4566_, v___x_4615_, v___y_4614_);
if (lean_obj_tag(v___x_4616_) == 0)
{
lean_object* v_a_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4624_; 
lean_dec(v_result_4612_);
lean_dec_ref(v___x_4610_);
lean_del_object(v___x_4570_);
lean_dec(v_fst_4564_);
lean_dec_ref(v_lctx_4525_);
lean_dec(v___x_4521_);
lean_dec(v_us_4520_);
v_a_4617_ = lean_ctor_get(v___x_4616_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4619_ = v___x_4616_;
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_a_4617_);
lean_dec(v___x_4616_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4624_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4622_; 
if (v_isShared_4620_ == 0)
{
v___x_4622_ = v___x_4619_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v_a_4617_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v_snd_4626_; lean_object* v_fst_4627_; lean_object* v_ngen_4628_; lean_object* v_nestedAux_4629_; lean_object* v_lvls_4630_; lean_object* v_newTypes_4631_; lean_object* v_nextIdx_4632_; lean_object* v___x_4634_; uint8_t v_isShared_4635_; uint8_t v_isSharedCheck_4644_; 
v_a_4625_ = lean_ctor_get(v___x_4616_, 0);
lean_inc(v_a_4625_);
lean_dec_ref(v___x_4616_);
v_snd_4626_ = lean_ctor_get(v_a_4625_, 1);
lean_inc(v_snd_4626_);
v_fst_4627_ = lean_ctor_get(v_a_4625_, 0);
lean_inc(v_fst_4627_);
lean_dec(v_a_4625_);
v_ngen_4628_ = lean_ctor_get(v_snd_4626_, 0);
v_nestedAux_4629_ = lean_ctor_get(v_snd_4626_, 1);
v_lvls_4630_ = lean_ctor_get(v_snd_4626_, 2);
v_newTypes_4631_ = lean_ctor_get(v_snd_4626_, 3);
v_nextIdx_4632_ = lean_ctor_get(v_snd_4626_, 4);
v_isSharedCheck_4644_ = !lean_is_exclusive(v_snd_4626_);
if (v_isSharedCheck_4644_ == 0)
{
v___x_4634_ = v_snd_4626_;
v_isShared_4635_ = v_isSharedCheck_4644_;
goto v_resetjp_4633_;
}
else
{
lean_inc(v_nextIdx_4632_);
lean_inc(v_newTypes_4631_);
lean_inc(v_lvls_4630_);
lean_inc(v_nestedAux_4629_);
lean_inc(v_ngen_4628_);
lean_dec(v_snd_4626_);
v___x_4634_ = lean_box(0);
v_isShared_4635_ = v_isSharedCheck_4644_;
goto v_resetjp_4633_;
}
v_resetjp_4633_:
{
lean_object* v___x_4637_; 
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 2, v_fst_4627_);
lean_ctor_set(v___x_4570_, 1, v___x_4610_);
lean_ctor_set(v___x_4570_, 0, v_fst_4564_);
v___x_4637_ = v___x_4570_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4643_; 
v_reuseFailAlloc_4643_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4643_, 0, v_fst_4564_);
lean_ctor_set(v_reuseFailAlloc_4643_, 1, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4643_, 2, v_fst_4627_);
v___x_4637_ = v_reuseFailAlloc_4643_;
goto v_reusejp_4636_;
}
v_reusejp_4636_:
{
lean_object* v___x_4638_; lean_object* v___x_4640_; 
v___x_4638_ = lean_array_push(v_newTypes_4631_, v___x_4637_);
if (v_isShared_4635_ == 0)
{
lean_ctor_set(v___x_4634_, 3, v___x_4638_);
v___x_4640_ = v___x_4634_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_ngen_4628_);
lean_ctor_set(v_reuseFailAlloc_4642_, 1, v_nestedAux_4629_);
lean_ctor_set(v_reuseFailAlloc_4642_, 2, v_lvls_4630_);
lean_ctor_set(v_reuseFailAlloc_4642_, 3, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4642_, 4, v_nextIdx_4632_);
v___x_4640_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
v_as_x27_4528_ = v_tail_4535_;
v_b_4529_ = v_result_4612_;
v___y_4531_ = v___x_4640_;
goto _start;
}
}
}
}
}
v_reusejp_4645_:
{
lean_object* v___x_4647_; lean_object* v___x_4649_; 
v___x_4647_ = lean_array_push(v_nestedAux_4601_, v___x_4646_);
lean_inc(v_lvls_4602_);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 1, v___x_4647_);
v___x_4649_ = v___x_4606_;
goto v_reusejp_4648_;
}
else
{
lean_object* v_reuseFailAlloc_4657_; 
v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_ngen_4600_);
lean_ctor_set(v_reuseFailAlloc_4657_, 1, v___x_4647_);
lean_ctor_set(v_reuseFailAlloc_4657_, 2, v_lvls_4602_);
lean_ctor_set(v_reuseFailAlloc_4657_, 3, v_newTypes_4603_);
lean_ctor_set(v_reuseFailAlloc_4657_, 4, v_nextIdx_4604_);
v___x_4649_ = v_reuseFailAlloc_4657_;
goto v_reusejp_4648_;
}
v_reusejp_4648_:
{
uint8_t v___x_4650_; 
v___x_4650_ = lean_name_eq(v_head_4534_, v_declName_4526_);
if (v___x_4650_ == 0)
{
lean_dec(v_lvls_4602_);
lean_del_object(v___x_4548_);
v_result_4612_ = v_b_4529_;
v___y_4613_ = v___y_4530_;
v___y_4614_ = v___x_4649_;
goto v___jp_4611_;
}
else
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4655_; 
lean_dec(v_b_4529_);
lean_inc(v_fst_4564_);
v___x_4651_ = l_Lean_Expr_const___override(v_fst_4564_, v_lvls_4602_);
v___x_4652_ = l_Lean_mkAppN(v___x_4651_, v_As_4524_);
lean_inc(v___x_4521_);
v___x_4653_ = l_Lean_mkAppRange(v___x_4652_, v___x_4521_, v___x_4527_, v_args_4522_);
if (v_isShared_4549_ == 0)
{
lean_ctor_set_tag(v___x_4548_, 1);
lean_ctor_set(v___x_4548_, 0, v___x_4653_);
v___x_4655_ = v___x_4548_;
goto v_reusejp_4654_;
}
else
{
lean_object* v_reuseFailAlloc_4656_; 
v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4653_);
v___x_4655_ = v_reuseFailAlloc_4656_;
goto v_reusejp_4654_;
}
v_reusejp_4654_:
{
v_result_4612_ = v___x_4655_;
v___y_4613_ = v___y_4530_;
v___y_4614_ = v___x_4649_;
goto v___jp_4611_;
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
else
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
lean_dec(v_a_4545_);
v___x_4664_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__3);
v___x_4665_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__2(v___x_4664_, v___y_4530_, v___y_4531_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4673_; 
lean_dec(v_b_4529_);
lean_dec_ref(v_lctx_4525_);
lean_dec(v___x_4521_);
lean_dec(v_us_4520_);
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4673_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4673_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4673_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
lean_object* v___x_4671_; 
if (v_isShared_4669_ == 0)
{
v___x_4671_ = v___x_4668_;
goto v_reusejp_4670_;
}
else
{
lean_object* v_reuseFailAlloc_4672_; 
v_reuseFailAlloc_4672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4672_, 0, v_a_4666_);
v___x_4671_ = v_reuseFailAlloc_4672_;
goto v_reusejp_4670_;
}
v_reusejp_4670_:
{
return v___x_4671_;
}
}
}
else
{
lean_object* v_a_4674_; lean_object* v_snd_4675_; 
v_a_4674_ = lean_ctor_get(v___x_4665_, 0);
lean_inc(v_a_4674_);
lean_dec_ref(v___x_4665_);
v_snd_4675_ = lean_ctor_get(v_a_4674_, 1);
lean_inc(v_snd_4675_);
lean_dec(v_a_4674_);
v_as_x27_4528_ = v_tail_4535_;
v___y_4531_ = v_snd_4675_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___boxed(lean_object* v___y_4677_, lean_object* v_us_4678_, lean_object* v___x_4679_, lean_object* v_args_4680_, lean_object* v_params_4681_, lean_object* v_As_4682_, lean_object* v_lctx_4683_, lean_object* v_declName_4684_, lean_object* v___x_4685_, lean_object* v_as_x27_4686_, lean_object* v_b_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg(v___y_4677_, v_us_4678_, v___x_4679_, v_args_4680_, v_params_4681_, v_As_4682_, v_lctx_4683_, v_declName_4684_, v___x_4685_, v_as_x27_4686_, v_b_4687_, v___y_4688_, v___y_4689_);
lean_dec_ref(v___y_4688_);
lean_dec(v_as_x27_4686_);
lean_dec(v___x_4685_);
lean_dec(v_declName_4684_);
lean_dec_ref(v_As_4682_);
lean_dec_ref(v_params_4681_);
lean_dec_ref(v_args_4680_);
lean_dec_ref(v___y_4677_);
return v_res_4690_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4(lean_object* v_fst_4694_, lean_object* v_as_4695_, size_t v_sz_4696_, size_t v_i_4697_, lean_object* v_b_4698_){
_start:
{
uint8_t v___x_4699_; 
v___x_4699_ = lean_usize_dec_lt(v_i_4697_, v_sz_4696_);
if (v___x_4699_ == 0)
{
lean_inc_ref(v_b_4698_);
return v_b_4698_;
}
else
{
lean_object* v_a_4700_; lean_object* v_fst_4701_; lean_object* v_snd_4702_; lean_object* v___x_4704_; uint8_t v_isShared_4705_; uint8_t v_isSharedCheck_4717_; 
v_a_4700_ = lean_array_uget(v_as_4695_, v_i_4697_);
v_fst_4701_ = lean_ctor_get(v_a_4700_, 0);
v_snd_4702_ = lean_ctor_get(v_a_4700_, 1);
v_isSharedCheck_4717_ = !lean_is_exclusive(v_a_4700_);
if (v_isSharedCheck_4717_ == 0)
{
v___x_4704_ = v_a_4700_;
v_isShared_4705_ = v_isSharedCheck_4717_;
goto v_resetjp_4703_;
}
else
{
lean_inc(v_snd_4702_);
lean_inc(v_fst_4701_);
lean_dec(v_a_4700_);
v___x_4704_ = lean_box(0);
v_isShared_4705_ = v_isSharedCheck_4717_;
goto v_resetjp_4703_;
}
v_resetjp_4703_:
{
lean_object* v___x_4706_; uint8_t v___x_4707_; 
v___x_4706_ = lean_box(0);
v___x_4707_ = lean_expr_eqv(v_fst_4701_, v_fst_4694_);
lean_dec(v_fst_4701_);
if (v___x_4707_ == 0)
{
lean_object* v___x_4708_; size_t v___x_4709_; size_t v___x_4710_; 
lean_del_object(v___x_4704_);
lean_dec(v_snd_4702_);
v___x_4708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4___closed__0));
v___x_4709_ = ((size_t)1ULL);
v___x_4710_ = lean_usize_add(v_i_4697_, v___x_4709_);
v_i_4697_ = v___x_4710_;
v_b_4698_ = v___x_4708_;
goto _start;
}
else
{
lean_object* v___x_4712_; lean_object* v___x_4713_; lean_object* v___x_4715_; 
v___x_4712_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4712_, 0, v_snd_4702_);
v___x_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4712_);
if (v_isShared_4705_ == 0)
{
lean_ctor_set(v___x_4704_, 1, v___x_4706_);
lean_ctor_set(v___x_4704_, 0, v___x_4713_);
v___x_4715_ = v___x_4704_;
goto v_reusejp_4714_;
}
else
{
lean_object* v_reuseFailAlloc_4716_; 
v_reuseFailAlloc_4716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4716_, 0, v___x_4713_);
lean_ctor_set(v_reuseFailAlloc_4716_, 1, v___x_4706_);
v___x_4715_ = v_reuseFailAlloc_4716_;
goto v_reusejp_4714_;
}
v_reusejp_4714_:
{
return v___x_4715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4___boxed(lean_object* v_fst_4718_, lean_object* v_as_4719_, lean_object* v_sz_4720_, lean_object* v_i_4721_, lean_object* v_b_4722_){
_start:
{
size_t v_sz_boxed_4723_; size_t v_i_boxed_4724_; lean_object* v_res_4725_; 
v_sz_boxed_4723_ = lean_unbox_usize(v_sz_4720_);
lean_dec(v_sz_4720_);
v_i_boxed_4724_ = lean_unbox_usize(v_i_4721_);
lean_dec(v_i_4721_);
v_res_4725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4(v_fst_4718_, v_as_4719_, v_sz_boxed_4723_, v_i_boxed_4724_, v_b_4722_);
lean_dec_ref(v_b_4722_);
lean_dec_ref(v_as_4719_);
lean_dec_ref(v_fst_4718_);
return v_res_4725_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__1(void){
_start:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; lean_object* v___x_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v___x_4727_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__0));
v___x_4728_ = lean_unsigned_to_nat(2u);
v___x_4729_ = lean_unsigned_to_nat(631u);
v___x_4730_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__2));
v___x_4731_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_4732_ = l_mkPanicMessageWithDecl(v___x_4731_, v___x_4730_, v___x_4729_, v___x_4728_, v___x_4727_);
return v___x_4732_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__3(void){
_start:
{
lean_object* v___x_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
v___x_4734_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__2));
v___x_4735_ = lean_unsigned_to_nat(2u);
v___x_4736_ = lean_unsigned_to_nat(662u);
v___x_4737_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__2));
v___x_4738_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_4739_ = l_mkPanicMessageWithDecl(v___x_4738_, v___x_4737_, v___x_4736_, v___x_4735_, v___x_4734_);
return v___x_4739_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__4(void){
_start:
{
lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v___x_4740_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_4741_ = lean_unsigned_to_nat(35u);
v___x_4742_ = lean_unsigned_to_nat(629u);
v___x_4743_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg___closed__2));
v___x_4744_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_4745_ = l_mkPanicMessageWithDecl(v___x_4744_, v___x_4743_, v___x_4742_, v___x_4741_, v___x_4740_);
return v___x_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5(lean_object* v_val_4746_, lean_object* v_params_4747_, lean_object* v_As_4748_, lean_object* v_lctx_4749_, lean_object* v_x_4750_, lean_object* v_x_4751_, lean_object* v_x_4752_, lean_object* v___y_4753_, lean_object* v___y_4754_){
_start:
{
if (lean_obj_tag(v_x_4750_) == 5)
{
lean_object* v_fn_4755_; lean_object* v_arg_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v_fn_4755_ = lean_ctor_get(v_x_4750_, 0);
lean_inc_ref(v_fn_4755_);
v_arg_4756_ = lean_ctor_get(v_x_4750_, 1);
lean_inc_ref(v_arg_4756_);
lean_dec_ref(v_x_4750_);
v___x_4757_ = lean_array_set(v_x_4751_, v_x_4752_, v_arg_4756_);
v___x_4758_ = lean_unsigned_to_nat(1u);
v___x_4759_ = lean_nat_sub(v_x_4752_, v___x_4758_);
lean_dec(v_x_4752_);
v_x_4750_ = v_fn_4755_;
v_x_4751_ = v___x_4757_;
v_x_4752_ = v___x_4759_;
goto _start;
}
else
{
lean_dec(v_x_4752_);
if (lean_obj_tag(v_x_4750_) == 4)
{
lean_object* v_declName_4761_; lean_object* v_us_4762_; lean_object* v_numParams_4763_; lean_object* v_all_4764_; lean_object* v___x_4765_; uint8_t v___x_4766_; 
v_declName_4761_ = lean_ctor_get(v_x_4750_, 0);
lean_inc(v_declName_4761_);
v_us_4762_ = lean_ctor_get(v_x_4750_, 1);
lean_inc(v_us_4762_);
v_numParams_4763_ = lean_ctor_get(v_val_4746_, 1);
lean_inc(v_numParams_4763_);
v_all_4764_ = lean_ctor_get(v_val_4746_, 3);
lean_inc(v_all_4764_);
lean_dec_ref(v_val_4746_);
v___x_4765_ = lean_array_get_size(v_x_4751_);
v___x_4766_ = lean_nat_dec_le(v_numParams_4763_, v___x_4765_);
if (v___x_4766_ == 0)
{
lean_object* v___x_4767_; lean_object* v___x_4768_; 
lean_dec(v_all_4764_);
lean_dec(v_numParams_4763_);
lean_dec(v_us_4762_);
lean_dec(v_declName_4761_);
lean_dec_ref(v_x_4750_);
lean_dec_ref(v_x_4751_);
lean_dec_ref(v_lctx_4749_);
v___x_4767_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__1, &l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__1_once, _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__1);
v___x_4768_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0(v___x_4767_, v___y_4753_, v___y_4754_);
return v___x_4768_;
}
else
{
lean_object* v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v___x_4769_ = lean_unsigned_to_nat(0u);
v___x_4770_ = l_Lean_mkAppRange(v_x_4750_, v___x_4769_, v_numParams_4763_, v_x_4751_);
v___x_4771_ = l_Lean4Lean_ElimNestedInductive_replaceParams(v_params_4747_, v___x_4770_, v_As_4748_, v___y_4753_, v___y_4754_);
lean_dec_ref(v___x_4770_);
if (lean_obj_tag(v___x_4771_) == 0)
{
lean_object* v_a_4772_; lean_object* v___x_4774_; uint8_t v_isShared_4775_; uint8_t v_isSharedCheck_4779_; 
lean_dec(v_all_4764_);
lean_dec(v_numParams_4763_);
lean_dec(v_us_4762_);
lean_dec(v_declName_4761_);
lean_dec_ref(v_x_4751_);
lean_dec_ref(v_lctx_4749_);
v_a_4772_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4779_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4779_ == 0)
{
v___x_4774_ = v___x_4771_;
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
else
{
lean_inc(v_a_4772_);
lean_dec(v___x_4771_);
v___x_4774_ = lean_box(0);
v_isShared_4775_ = v_isSharedCheck_4779_;
goto v_resetjp_4773_;
}
v_resetjp_4773_:
{
lean_object* v___x_4777_; 
if (v_isShared_4775_ == 0)
{
v___x_4777_ = v___x_4774_;
goto v_reusejp_4776_;
}
else
{
lean_object* v_reuseFailAlloc_4778_; 
v_reuseFailAlloc_4778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4778_, 0, v_a_4772_);
v___x_4777_ = v_reuseFailAlloc_4778_;
goto v_reusejp_4776_;
}
v_reusejp_4776_:
{
return v___x_4777_;
}
}
}
else
{
lean_object* v_a_4780_; lean_object* v___x_4782_; uint8_t v_isShared_4783_; uint8_t v_isSharedCheck_4824_; 
v_a_4780_ = lean_ctor_get(v___x_4771_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4771_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4782_ = v___x_4771_;
v_isShared_4783_ = v_isSharedCheck_4824_;
goto v_resetjp_4781_;
}
else
{
lean_inc(v_a_4780_);
lean_dec(v___x_4771_);
v___x_4782_ = lean_box(0);
v_isShared_4783_ = v_isSharedCheck_4824_;
goto v_resetjp_4781_;
}
v_resetjp_4781_:
{
lean_object* v_fst_4784_; lean_object* v_snd_4785_; lean_object* v_nestedAux_4794_; lean_object* v_lvls_4795_; lean_object* v___x_4796_; size_t v_sz_4797_; size_t v___x_4798_; lean_object* v___x_4799_; lean_object* v_fst_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4822_; 
v_fst_4784_ = lean_ctor_get(v_a_4780_, 0);
lean_inc(v_fst_4784_);
v_snd_4785_ = lean_ctor_get(v_a_4780_, 1);
lean_inc(v_snd_4785_);
lean_dec(v_a_4780_);
v_nestedAux_4794_ = lean_ctor_get(v_snd_4785_, 1);
v_lvls_4795_ = lean_ctor_get(v_snd_4785_, 2);
v___x_4796_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4___closed__0));
v_sz_4797_ = lean_array_size(v_nestedAux_4794_);
v___x_4798_ = ((size_t)0ULL);
v___x_4799_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__4(v_fst_4784_, v_nestedAux_4794_, v_sz_4797_, v___x_4798_, v___x_4796_);
lean_dec(v_fst_4784_);
v_fst_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4822_ == 0)
{
lean_object* v_unused_4823_; 
v_unused_4823_ = lean_ctor_get(v___x_4799_, 1);
lean_dec(v_unused_4823_);
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4822_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_fst_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4822_;
goto v_resetjp_4801_;
}
v___jp_4786_:
{
lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4787_ = lean_box(0);
v___x_4788_ = l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg(v___y_4753_, v_us_4762_, v_numParams_4763_, v_x_4751_, v_params_4747_, v_As_4748_, v_lctx_4749_, v_declName_4761_, v___x_4765_, v_all_4764_, v___x_4787_, v___y_4753_, v_snd_4785_);
lean_dec(v_all_4764_);
lean_dec(v_declName_4761_);
lean_dec_ref(v_x_4751_);
if (lean_obj_tag(v___x_4788_) == 0)
{
return v___x_4788_;
}
else
{
lean_object* v_a_4789_; lean_object* v_fst_4790_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc(v_a_4789_);
v_fst_4790_ = lean_ctor_get(v_a_4789_, 0);
if (lean_obj_tag(v_fst_4790_) == 0)
{
lean_object* v_snd_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; 
lean_dec_ref(v___x_4788_);
v_snd_4791_ = lean_ctor_get(v_a_4789_, 1);
lean_inc(v_snd_4791_);
lean_dec(v_a_4789_);
v___x_4792_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__3, &l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__3_once, _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__3);
v___x_4793_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0(v___x_4792_, v___y_4753_, v_snd_4791_);
return v___x_4793_;
}
else
{
lean_dec(v_a_4789_);
return v___x_4788_;
}
}
}
v_resetjp_4801_:
{
if (lean_obj_tag(v_fst_4800_) == 0)
{
lean_del_object(v___x_4802_);
lean_del_object(v___x_4782_);
goto v___jp_4786_;
}
else
{
lean_object* v_val_4804_; 
v_val_4804_ = lean_ctor_get(v_fst_4800_, 0);
lean_inc(v_val_4804_);
lean_dec_ref(v_fst_4800_);
if (lean_obj_tag(v_val_4804_) == 1)
{
lean_object* v_val_4805_; lean_object* v___x_4807_; uint8_t v_isShared_4808_; uint8_t v_isSharedCheck_4821_; 
lean_dec(v_all_4764_);
lean_dec(v_us_4762_);
lean_dec(v_declName_4761_);
lean_dec_ref(v_lctx_4749_);
v_val_4805_ = lean_ctor_get(v_val_4804_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v_val_4804_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4807_ = v_val_4804_;
v_isShared_4808_ = v_isSharedCheck_4821_;
goto v_resetjp_4806_;
}
else
{
lean_inc(v_val_4805_);
lean_dec(v_val_4804_);
v___x_4807_ = lean_box(0);
v_isShared_4808_ = v_isSharedCheck_4821_;
goto v_resetjp_4806_;
}
v_resetjp_4806_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4813_; 
lean_inc(v_lvls_4795_);
v___x_4809_ = l_Lean_Expr_const___override(v_val_4805_, v_lvls_4795_);
v___x_4810_ = l_Lean_mkAppN(v___x_4809_, v_As_4748_);
v___x_4811_ = l_Lean_mkAppRange(v___x_4810_, v_numParams_4763_, v___x_4765_, v_x_4751_);
lean_dec_ref(v_x_4751_);
if (v_isShared_4808_ == 0)
{
lean_ctor_set(v___x_4807_, 0, v___x_4811_);
v___x_4813_ = v___x_4807_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4811_);
v___x_4813_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
lean_object* v___x_4815_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 1, v_snd_4785_);
lean_ctor_set(v___x_4802_, 0, v___x_4813_);
v___x_4815_ = v___x_4802_;
goto v_reusejp_4814_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v___x_4813_);
lean_ctor_set(v_reuseFailAlloc_4819_, 1, v_snd_4785_);
v___x_4815_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4814_;
}
v_reusejp_4814_:
{
lean_object* v___x_4817_; 
if (v_isShared_4783_ == 0)
{
lean_ctor_set(v___x_4782_, 0, v___x_4815_);
v___x_4817_ = v___x_4782_;
goto v_reusejp_4816_;
}
else
{
lean_object* v_reuseFailAlloc_4818_; 
v_reuseFailAlloc_4818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4818_, 0, v___x_4815_);
v___x_4817_ = v_reuseFailAlloc_4818_;
goto v_reusejp_4816_;
}
v_reusejp_4816_:
{
return v___x_4817_;
}
}
}
}
}
else
{
lean_dec(v_val_4804_);
lean_del_object(v___x_4802_);
lean_del_object(v___x_4782_);
goto v___jp_4786_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4825_; lean_object* v___x_4826_; 
lean_dec_ref(v_x_4751_);
lean_dec_ref(v_x_4750_);
lean_dec_ref(v_lctx_4749_);
lean_dec_ref(v_val_4746_);
v___x_4825_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__4, &l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___closed__4);
v___x_4826_ = l_panic___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__0(v___x_4825_, v___y_4753_, v___y_4754_);
return v___x_4826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5___boxed(lean_object* v_val_4827_, lean_object* v_params_4828_, lean_object* v_As_4829_, lean_object* v_lctx_4830_, lean_object* v_x_4831_, lean_object* v_x_4832_, lean_object* v_x_4833_, lean_object* v___y_4834_, lean_object* v___y_4835_){
_start:
{
lean_object* v_res_4836_; 
v_res_4836_ = l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5(v_val_4827_, v_params_4828_, v_As_4829_, v_lctx_4830_, v_x_4831_, v_x_4832_, v_x_4833_, v___y_4834_, v___y_4835_);
lean_dec_ref(v___y_4834_);
lean_dec_ref(v_As_4829_);
lean_dec_ref(v_params_4828_);
return v_res_4836_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceIfNested(lean_object* v_lctx_4837_, lean_object* v_params_4838_, lean_object* v_As_4839_, lean_object* v_e_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
lean_object* v___x_4843_; 
lean_inc_ref(v_e_4840_);
v___x_4843_ = l_Lean4Lean_ElimNestedInductive_isNestedInductiveApp_x3f(v_e_4840_, v_a_4841_, v_a_4842_);
if (lean_obj_tag(v___x_4843_) == 0)
{
lean_object* v_a_4844_; lean_object* v___x_4846_; uint8_t v_isShared_4847_; uint8_t v_isSharedCheck_4851_; 
lean_dec_ref(v_e_4840_);
lean_dec_ref(v_lctx_4837_);
v_a_4844_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4851_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4851_ == 0)
{
v___x_4846_ = v___x_4843_;
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
else
{
lean_inc(v_a_4844_);
lean_dec(v___x_4843_);
v___x_4846_ = lean_box(0);
v_isShared_4847_ = v_isSharedCheck_4851_;
goto v_resetjp_4845_;
}
v_resetjp_4845_:
{
lean_object* v___x_4849_; 
if (v_isShared_4847_ == 0)
{
v___x_4849_ = v___x_4846_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4850_; 
v_reuseFailAlloc_4850_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_a_4844_);
v___x_4849_ = v_reuseFailAlloc_4850_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
return v___x_4849_;
}
}
}
else
{
lean_object* v_a_4852_; lean_object* v___x_4854_; uint8_t v_isShared_4855_; uint8_t v_isSharedCheck_4878_; 
v_a_4852_ = lean_ctor_get(v___x_4843_, 0);
v_isSharedCheck_4878_ = !lean_is_exclusive(v___x_4843_);
if (v_isSharedCheck_4878_ == 0)
{
v___x_4854_ = v___x_4843_;
v_isShared_4855_ = v_isSharedCheck_4878_;
goto v_resetjp_4853_;
}
else
{
lean_inc(v_a_4852_);
lean_dec(v___x_4843_);
v___x_4854_ = lean_box(0);
v_isShared_4855_ = v_isSharedCheck_4878_;
goto v_resetjp_4853_;
}
v_resetjp_4853_:
{
lean_object* v_fst_4856_; 
v_fst_4856_ = lean_ctor_get(v_a_4852_, 0);
if (lean_obj_tag(v_fst_4856_) == 1)
{
lean_object* v_snd_4857_; lean_object* v_val_4858_; lean_object* v_dummy_4859_; lean_object* v_nargs_4860_; lean_object* v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; 
lean_inc_ref(v_fst_4856_);
lean_del_object(v___x_4854_);
v_snd_4857_ = lean_ctor_get(v_a_4852_, 1);
lean_inc(v_snd_4857_);
lean_dec(v_a_4852_);
v_val_4858_ = lean_ctor_get(v_fst_4856_, 0);
lean_inc(v_val_4858_);
lean_dec_ref(v_fst_4856_);
v_dummy_4859_ = lean_obj_once(&l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0, &l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0_once, _init_l_Lean4Lean_AddInductive_isValidIndAppIdx___closed__0);
v_nargs_4860_ = l_Lean_Expr_getAppNumArgs(v_e_4840_);
lean_inc(v_nargs_4860_);
v___x_4861_ = lean_mk_array(v_nargs_4860_, v_dummy_4859_);
v___x_4862_ = lean_unsigned_to_nat(1u);
v___x_4863_ = lean_nat_sub(v_nargs_4860_, v___x_4862_);
lean_dec(v_nargs_4860_);
v___x_4864_ = l_Lean_Expr_withAppAux___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__5(v_val_4858_, v_params_4838_, v_As_4839_, v_lctx_4837_, v_e_4840_, v___x_4861_, v___x_4863_, v_a_4841_, v_snd_4857_);
return v___x_4864_;
}
else
{
lean_object* v_snd_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4876_; 
lean_dec_ref(v_e_4840_);
lean_dec_ref(v_lctx_4837_);
v_snd_4865_ = lean_ctor_get(v_a_4852_, 1);
v_isSharedCheck_4876_ = !lean_is_exclusive(v_a_4852_);
if (v_isSharedCheck_4876_ == 0)
{
lean_object* v_unused_4877_; 
v_unused_4877_ = lean_ctor_get(v_a_4852_, 0);
lean_dec(v_unused_4877_);
v___x_4867_ = v_a_4852_;
v_isShared_4868_ = v_isSharedCheck_4876_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_snd_4865_);
lean_dec(v_a_4852_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4876_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
lean_object* v___x_4869_; lean_object* v___x_4871_; 
v___x_4869_ = lean_box(0);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 0, v___x_4869_);
v___x_4871_ = v___x_4867_;
goto v_reusejp_4870_;
}
else
{
lean_object* v_reuseFailAlloc_4875_; 
v_reuseFailAlloc_4875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4875_, 0, v___x_4869_);
lean_ctor_set(v_reuseFailAlloc_4875_, 1, v_snd_4865_);
v___x_4871_ = v_reuseFailAlloc_4875_;
goto v_reusejp_4870_;
}
v_reusejp_4870_:
{
lean_object* v___x_4873_; 
if (v_isShared_4855_ == 0)
{
lean_ctor_set(v___x_4854_, 0, v___x_4871_);
v___x_4873_ = v___x_4854_;
goto v_reusejp_4872_;
}
else
{
lean_object* v_reuseFailAlloc_4874_; 
v_reuseFailAlloc_4874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4874_, 0, v___x_4871_);
v___x_4873_ = v_reuseFailAlloc_4874_;
goto v_reusejp_4872_;
}
v_reusejp_4872_:
{
return v___x_4873_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceIfNested___boxed(lean_object* v_lctx_4879_, lean_object* v_params_4880_, lean_object* v_As_4881_, lean_object* v_e_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_){
_start:
{
lean_object* v_res_4885_; 
v_res_4885_ = l_Lean4Lean_ElimNestedInductive_replaceIfNested(v_lctx_4879_, v_params_4880_, v_As_4881_, v_e_4882_, v_a_4883_, v_a_4884_);
lean_dec_ref(v_a_4883_);
lean_dec_ref(v_As_4881_);
lean_dec_ref(v_params_4880_);
return v_res_4885_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1(lean_object* v___y_4886_, lean_object* v_us_4887_, lean_object* v___x_4888_, lean_object* v_args_4889_, lean_object* v_a_4890_, lean_object* v_fst_4891_, lean_object* v_lctx_4892_, lean_object* v_As_4893_, lean_object* v_x_4894_, lean_object* v_x_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v___x_4898_; 
v___x_4898_ = l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___redArg(v___y_4886_, v_us_4887_, v___x_4888_, v_args_4889_, v_a_4890_, v_fst_4891_, v_lctx_4892_, v_As_4893_, v_x_4894_, v_x_4895_, v___y_4897_);
return v___x_4898_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1___boxed(lean_object* v___y_4899_, lean_object* v_us_4900_, lean_object* v___x_4901_, lean_object* v_args_4902_, lean_object* v_a_4903_, lean_object* v_fst_4904_, lean_object* v_lctx_4905_, lean_object* v_As_4906_, lean_object* v_x_4907_, lean_object* v_x_4908_, lean_object* v___y_4909_, lean_object* v___y_4910_){
_start:
{
lean_object* v_res_4911_; 
v_res_4911_ = l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__1(v___y_4899_, v_us_4900_, v___x_4901_, v_args_4902_, v_a_4903_, v_fst_4904_, v_lctx_4905_, v_As_4906_, v_x_4907_, v_x_4908_, v___y_4909_, v___y_4910_);
lean_dec_ref(v___y_4909_);
lean_dec_ref(v_As_4906_);
lean_dec(v_fst_4904_);
lean_dec(v_a_4903_);
lean_dec_ref(v_args_4902_);
lean_dec_ref(v___y_4899_);
return v_res_4911_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3(lean_object* v___y_4912_, lean_object* v_us_4913_, lean_object* v___x_4914_, lean_object* v_args_4915_, lean_object* v_params_4916_, lean_object* v_As_4917_, lean_object* v_lctx_4918_, lean_object* v_declName_4919_, lean_object* v___x_4920_, lean_object* v_as_4921_, lean_object* v_as_x27_4922_, lean_object* v_b_4923_, lean_object* v_a_4924_, lean_object* v___y_4925_, lean_object* v___y_4926_){
_start:
{
lean_object* v___x_4927_; 
v___x_4927_ = l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___redArg(v___y_4912_, v_us_4913_, v___x_4914_, v_args_4915_, v_params_4916_, v_As_4917_, v_lctx_4918_, v_declName_4919_, v___x_4920_, v_as_x27_4922_, v_b_4923_, v___y_4925_, v___y_4926_);
return v___x_4927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3___boxed(lean_object* v___y_4928_, lean_object* v_us_4929_, lean_object* v___x_4930_, lean_object* v_args_4931_, lean_object* v_params_4932_, lean_object* v_As_4933_, lean_object* v_lctx_4934_, lean_object* v_declName_4935_, lean_object* v___x_4936_, lean_object* v_as_4937_, lean_object* v_as_x27_4938_, lean_object* v_b_4939_, lean_object* v_a_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v_res_4943_; 
v_res_4943_ = l_List_forIn_x27_loop___at___00Lean4Lean_ElimNestedInductive_replaceIfNested_spec__3(v___y_4928_, v_us_4929_, v___x_4930_, v_args_4931_, v_params_4932_, v_As_4933_, v_lctx_4934_, v_declName_4935_, v___x_4936_, v_as_4937_, v_as_x27_4938_, v_b_4939_, v_a_4940_, v___y_4941_, v___y_4942_);
lean_dec_ref(v___y_4941_);
lean_dec(v_as_x27_4938_);
lean_dec(v_as_4937_);
lean_dec(v___x_4936_);
lean_dec(v_declName_4935_);
lean_dec_ref(v_As_4933_);
lean_dec_ref(v_params_4932_);
lean_dec_ref(v_args_4931_);
lean_dec_ref(v___y_4928_);
return v_res_4943_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___redArg(lean_object* v_a_4944_, lean_object* v_x_4945_){
_start:
{
if (lean_obj_tag(v_x_4945_) == 0)
{
uint8_t v___x_4946_; 
v___x_4946_ = 0;
return v___x_4946_;
}
else
{
lean_object* v_key_4947_; lean_object* v_tail_4948_; size_t v___x_4949_; size_t v___x_4950_; uint8_t v___x_4951_; 
v_key_4947_ = lean_ctor_get(v_x_4945_, 0);
v_tail_4948_ = lean_ctor_get(v_x_4945_, 2);
v___x_4949_ = lean_ptr_addr(v_key_4947_);
v___x_4950_ = lean_ptr_addr(v_a_4944_);
v___x_4951_ = lean_usize_dec_eq(v___x_4949_, v___x_4950_);
if (v___x_4951_ == 0)
{
v_x_4945_ = v_tail_4948_;
goto _start;
}
else
{
return v___x_4951_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_a_4953_, lean_object* v_x_4954_){
_start:
{
uint8_t v_res_4955_; lean_object* v_r_4956_; 
v_res_4955_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___redArg(v_a_4953_, v_x_4954_);
lean_dec(v_x_4954_);
lean_dec_ref(v_a_4953_);
v_r_4956_ = lean_box(v_res_4955_);
return v_r_4956_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(lean_object* v_x_4957_, lean_object* v_x_4958_){
_start:
{
if (lean_obj_tag(v_x_4958_) == 0)
{
return v_x_4957_;
}
else
{
lean_object* v_key_4959_; lean_object* v_value_4960_; lean_object* v_tail_4961_; lean_object* v___x_4963_; uint8_t v_isShared_4964_; uint8_t v_isSharedCheck_4987_; 
v_key_4959_ = lean_ctor_get(v_x_4958_, 0);
v_value_4960_ = lean_ctor_get(v_x_4958_, 1);
v_tail_4961_ = lean_ctor_get(v_x_4958_, 2);
v_isSharedCheck_4987_ = !lean_is_exclusive(v_x_4958_);
if (v_isSharedCheck_4987_ == 0)
{
v___x_4963_ = v_x_4958_;
v_isShared_4964_ = v_isSharedCheck_4987_;
goto v_resetjp_4962_;
}
else
{
lean_inc(v_tail_4961_);
lean_inc(v_value_4960_);
lean_inc(v_key_4959_);
lean_dec(v_x_4958_);
v___x_4963_ = lean_box(0);
v_isShared_4964_ = v_isSharedCheck_4987_;
goto v_resetjp_4962_;
}
v_resetjp_4962_:
{
lean_object* v___x_4965_; size_t v___x_4966_; uint64_t v___x_4967_; uint64_t v___x_4968_; uint64_t v___x_4969_; uint64_t v___x_4970_; uint64_t v___x_4971_; uint64_t v_fold_4972_; uint64_t v___x_4973_; uint64_t v___x_4974_; uint64_t v___x_4975_; size_t v___x_4976_; size_t v___x_4977_; size_t v___x_4978_; size_t v___x_4979_; size_t v___x_4980_; lean_object* v___x_4981_; lean_object* v___x_4983_; 
v___x_4965_ = lean_array_get_size(v_x_4957_);
v___x_4966_ = lean_ptr_addr(v_key_4959_);
v___x_4967_ = lean_usize_to_uint64(v___x_4966_);
v___x_4968_ = 11ULL;
v___x_4969_ = lean_uint64_mix_hash(v___x_4967_, v___x_4968_);
v___x_4970_ = 32ULL;
v___x_4971_ = lean_uint64_shift_right(v___x_4969_, v___x_4970_);
v_fold_4972_ = lean_uint64_xor(v___x_4969_, v___x_4971_);
v___x_4973_ = 16ULL;
v___x_4974_ = lean_uint64_shift_right(v_fold_4972_, v___x_4973_);
v___x_4975_ = lean_uint64_xor(v_fold_4972_, v___x_4974_);
v___x_4976_ = lean_uint64_to_usize(v___x_4975_);
v___x_4977_ = lean_usize_of_nat(v___x_4965_);
v___x_4978_ = ((size_t)1ULL);
v___x_4979_ = lean_usize_sub(v___x_4977_, v___x_4978_);
v___x_4980_ = lean_usize_land(v___x_4976_, v___x_4979_);
v___x_4981_ = lean_array_uget_borrowed(v_x_4957_, v___x_4980_);
lean_inc(v___x_4981_);
if (v_isShared_4964_ == 0)
{
lean_ctor_set(v___x_4963_, 2, v___x_4981_);
v___x_4983_ = v___x_4963_;
goto v_reusejp_4982_;
}
else
{
lean_object* v_reuseFailAlloc_4986_; 
v_reuseFailAlloc_4986_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_4986_, 0, v_key_4959_);
lean_ctor_set(v_reuseFailAlloc_4986_, 1, v_value_4960_);
lean_ctor_set(v_reuseFailAlloc_4986_, 2, v___x_4981_);
v___x_4983_ = v_reuseFailAlloc_4986_;
goto v_reusejp_4982_;
}
v_reusejp_4982_:
{
lean_object* v___x_4984_; 
v___x_4984_ = lean_array_uset(v_x_4957_, v___x_4980_, v___x_4983_);
v_x_4957_ = v___x_4984_;
v_x_4958_ = v_tail_4961_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5___redArg(lean_object* v_i_4988_, lean_object* v_source_4989_, lean_object* v_target_4990_){
_start:
{
lean_object* v___x_4991_; uint8_t v___x_4992_; 
v___x_4991_ = lean_array_get_size(v_source_4989_);
v___x_4992_ = lean_nat_dec_lt(v_i_4988_, v___x_4991_);
if (v___x_4992_ == 0)
{
lean_dec_ref(v_source_4989_);
lean_dec(v_i_4988_);
return v_target_4990_;
}
else
{
lean_object* v_es_4993_; lean_object* v___x_4994_; lean_object* v_source_4995_; lean_object* v_target_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v_es_4993_ = lean_array_fget(v_source_4989_, v_i_4988_);
v___x_4994_ = lean_box(0);
v_source_4995_ = lean_array_fset(v_source_4989_, v_i_4988_, v___x_4994_);
v_target_4996_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_target_4990_, v_es_4993_);
v___x_4997_ = lean_unsigned_to_nat(1u);
v___x_4998_ = lean_nat_add(v_i_4988_, v___x_4997_);
lean_dec(v_i_4988_);
v_i_4988_ = v___x_4998_;
v_source_4989_ = v_source_4995_;
v_target_4990_ = v_target_4996_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4___redArg(lean_object* v_data_5000_){
_start:
{
lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v_nbuckets_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; 
v___x_5001_ = lean_array_get_size(v_data_5000_);
v___x_5002_ = lean_unsigned_to_nat(2u);
v_nbuckets_5003_ = lean_nat_mul(v___x_5001_, v___x_5002_);
v___x_5004_ = lean_unsigned_to_nat(0u);
v___x_5005_ = lean_box(0);
v___x_5006_ = lean_mk_array(v_nbuckets_5003_, v___x_5005_);
v___x_5007_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5___redArg(v___x_5004_, v_data_5000_, v___x_5006_);
return v___x_5007_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__5___redArg(lean_object* v_a_5008_, lean_object* v_b_5009_, lean_object* v_x_5010_){
_start:
{
if (lean_obj_tag(v_x_5010_) == 0)
{
lean_dec(v_b_5009_);
lean_dec_ref(v_a_5008_);
return v_x_5010_;
}
else
{
lean_object* v_key_5011_; lean_object* v_value_5012_; lean_object* v_tail_5013_; lean_object* v___x_5015_; uint8_t v_isShared_5016_; uint8_t v_isSharedCheck_5027_; 
v_key_5011_ = lean_ctor_get(v_x_5010_, 0);
v_value_5012_ = lean_ctor_get(v_x_5010_, 1);
v_tail_5013_ = lean_ctor_get(v_x_5010_, 2);
v_isSharedCheck_5027_ = !lean_is_exclusive(v_x_5010_);
if (v_isSharedCheck_5027_ == 0)
{
v___x_5015_ = v_x_5010_;
v_isShared_5016_ = v_isSharedCheck_5027_;
goto v_resetjp_5014_;
}
else
{
lean_inc(v_tail_5013_);
lean_inc(v_value_5012_);
lean_inc(v_key_5011_);
lean_dec(v_x_5010_);
v___x_5015_ = lean_box(0);
v_isShared_5016_ = v_isSharedCheck_5027_;
goto v_resetjp_5014_;
}
v_resetjp_5014_:
{
size_t v___x_5017_; size_t v___x_5018_; uint8_t v___x_5019_; 
v___x_5017_ = lean_ptr_addr(v_key_5011_);
v___x_5018_ = lean_ptr_addr(v_a_5008_);
v___x_5019_ = lean_usize_dec_eq(v___x_5017_, v___x_5018_);
if (v___x_5019_ == 0)
{
lean_object* v___x_5020_; lean_object* v___x_5022_; 
v___x_5020_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__5___redArg(v_a_5008_, v_b_5009_, v_tail_5013_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 2, v___x_5020_);
v___x_5022_ = v___x_5015_;
goto v_reusejp_5021_;
}
else
{
lean_object* v_reuseFailAlloc_5023_; 
v_reuseFailAlloc_5023_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5023_, 0, v_key_5011_);
lean_ctor_set(v_reuseFailAlloc_5023_, 1, v_value_5012_);
lean_ctor_set(v_reuseFailAlloc_5023_, 2, v___x_5020_);
v___x_5022_ = v_reuseFailAlloc_5023_;
goto v_reusejp_5021_;
}
v_reusejp_5021_:
{
return v___x_5022_;
}
}
else
{
lean_object* v___x_5025_; 
lean_dec(v_value_5012_);
lean_dec(v_key_5011_);
if (v_isShared_5016_ == 0)
{
lean_ctor_set(v___x_5015_, 1, v_b_5009_);
lean_ctor_set(v___x_5015_, 0, v_a_5008_);
v___x_5025_ = v___x_5015_;
goto v_reusejp_5024_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v_a_5008_);
lean_ctor_set(v_reuseFailAlloc_5026_, 1, v_b_5009_);
lean_ctor_set(v_reuseFailAlloc_5026_, 2, v_tail_5013_);
v___x_5025_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5024_;
}
v_reusejp_5024_:
{
return v___x_5025_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(lean_object* v_m_5028_, lean_object* v_a_5029_, lean_object* v_b_5030_){
_start:
{
lean_object* v_size_5031_; lean_object* v_buckets_5032_; lean_object* v___x_5034_; uint8_t v_isShared_5035_; uint8_t v_isSharedCheck_5078_; 
v_size_5031_ = lean_ctor_get(v_m_5028_, 0);
v_buckets_5032_ = lean_ctor_get(v_m_5028_, 1);
v_isSharedCheck_5078_ = !lean_is_exclusive(v_m_5028_);
if (v_isSharedCheck_5078_ == 0)
{
v___x_5034_ = v_m_5028_;
v_isShared_5035_ = v_isSharedCheck_5078_;
goto v_resetjp_5033_;
}
else
{
lean_inc(v_buckets_5032_);
lean_inc(v_size_5031_);
lean_dec(v_m_5028_);
v___x_5034_ = lean_box(0);
v_isShared_5035_ = v_isSharedCheck_5078_;
goto v_resetjp_5033_;
}
v_resetjp_5033_:
{
lean_object* v___x_5036_; size_t v___x_5037_; uint64_t v___x_5038_; uint64_t v___x_5039_; uint64_t v___x_5040_; uint64_t v___x_5041_; uint64_t v___x_5042_; uint64_t v_fold_5043_; uint64_t v___x_5044_; uint64_t v___x_5045_; uint64_t v___x_5046_; size_t v___x_5047_; size_t v___x_5048_; size_t v___x_5049_; size_t v___x_5050_; size_t v___x_5051_; lean_object* v_bkt_5052_; uint8_t v___x_5053_; 
v___x_5036_ = lean_array_get_size(v_buckets_5032_);
v___x_5037_ = lean_ptr_addr(v_a_5029_);
v___x_5038_ = lean_usize_to_uint64(v___x_5037_);
v___x_5039_ = 11ULL;
v___x_5040_ = lean_uint64_mix_hash(v___x_5038_, v___x_5039_);
v___x_5041_ = 32ULL;
v___x_5042_ = lean_uint64_shift_right(v___x_5040_, v___x_5041_);
v_fold_5043_ = lean_uint64_xor(v___x_5040_, v___x_5042_);
v___x_5044_ = 16ULL;
v___x_5045_ = lean_uint64_shift_right(v_fold_5043_, v___x_5044_);
v___x_5046_ = lean_uint64_xor(v_fold_5043_, v___x_5045_);
v___x_5047_ = lean_uint64_to_usize(v___x_5046_);
v___x_5048_ = lean_usize_of_nat(v___x_5036_);
v___x_5049_ = ((size_t)1ULL);
v___x_5050_ = lean_usize_sub(v___x_5048_, v___x_5049_);
v___x_5051_ = lean_usize_land(v___x_5047_, v___x_5050_);
v_bkt_5052_ = lean_array_uget_borrowed(v_buckets_5032_, v___x_5051_);
v___x_5053_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___redArg(v_a_5029_, v_bkt_5052_);
if (v___x_5053_ == 0)
{
lean_object* v___x_5054_; lean_object* v_size_x27_5055_; lean_object* v___x_5056_; lean_object* v_buckets_x27_5057_; lean_object* v___x_5058_; lean_object* v___x_5059_; lean_object* v___x_5060_; lean_object* v___x_5061_; lean_object* v___x_5062_; uint8_t v___x_5063_; 
v___x_5054_ = lean_unsigned_to_nat(1u);
v_size_x27_5055_ = lean_nat_add(v_size_5031_, v___x_5054_);
lean_dec(v_size_5031_);
lean_inc(v_bkt_5052_);
v___x_5056_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_5056_, 0, v_a_5029_);
lean_ctor_set(v___x_5056_, 1, v_b_5030_);
lean_ctor_set(v___x_5056_, 2, v_bkt_5052_);
v_buckets_x27_5057_ = lean_array_uset(v_buckets_5032_, v___x_5051_, v___x_5056_);
v___x_5058_ = lean_unsigned_to_nat(4u);
v___x_5059_ = lean_nat_mul(v_size_x27_5055_, v___x_5058_);
v___x_5060_ = lean_unsigned_to_nat(3u);
v___x_5061_ = lean_nat_div(v___x_5059_, v___x_5060_);
lean_dec(v___x_5059_);
v___x_5062_ = lean_array_get_size(v_buckets_x27_5057_);
v___x_5063_ = lean_nat_dec_le(v___x_5061_, v___x_5062_);
lean_dec(v___x_5061_);
if (v___x_5063_ == 0)
{
lean_object* v_val_5064_; lean_object* v___x_5066_; 
v_val_5064_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4___redArg(v_buckets_x27_5057_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 1, v_val_5064_);
lean_ctor_set(v___x_5034_, 0, v_size_x27_5055_);
v___x_5066_ = v___x_5034_;
goto v_reusejp_5065_;
}
else
{
lean_object* v_reuseFailAlloc_5067_; 
v_reuseFailAlloc_5067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5067_, 0, v_size_x27_5055_);
lean_ctor_set(v_reuseFailAlloc_5067_, 1, v_val_5064_);
v___x_5066_ = v_reuseFailAlloc_5067_;
goto v_reusejp_5065_;
}
v_reusejp_5065_:
{
return v___x_5066_;
}
}
else
{
lean_object* v___x_5069_; 
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 1, v_buckets_x27_5057_);
lean_ctor_set(v___x_5034_, 0, v_size_x27_5055_);
v___x_5069_ = v___x_5034_;
goto v_reusejp_5068_;
}
else
{
lean_object* v_reuseFailAlloc_5070_; 
v_reuseFailAlloc_5070_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5070_, 0, v_size_x27_5055_);
lean_ctor_set(v_reuseFailAlloc_5070_, 1, v_buckets_x27_5057_);
v___x_5069_ = v_reuseFailAlloc_5070_;
goto v_reusejp_5068_;
}
v_reusejp_5068_:
{
return v___x_5069_;
}
}
}
else
{
lean_object* v___x_5071_; lean_object* v_buckets_x27_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v___x_5076_; 
lean_inc(v_bkt_5052_);
v___x_5071_ = lean_box(0);
v_buckets_x27_5072_ = lean_array_uset(v_buckets_5032_, v___x_5051_, v___x_5071_);
v___x_5073_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__5___redArg(v_a_5029_, v_b_5030_, v_bkt_5052_);
v___x_5074_ = lean_array_uset(v_buckets_x27_5072_, v___x_5051_, v___x_5073_);
if (v_isShared_5035_ == 0)
{
lean_ctor_set(v___x_5034_, 1, v___x_5074_);
v___x_5076_ = v___x_5034_;
goto v_reusejp_5075_;
}
else
{
lean_object* v_reuseFailAlloc_5077_; 
v_reuseFailAlloc_5077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5077_, 0, v_size_5031_);
lean_ctor_set(v_reuseFailAlloc_5077_, 1, v___x_5074_);
v___x_5076_ = v_reuseFailAlloc_5077_;
goto v_reusejp_5075_;
}
v_reusejp_5075_:
{
return v___x_5076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___redArg(lean_object* v_a_5079_, lean_object* v_x_5080_){
_start:
{
if (lean_obj_tag(v_x_5080_) == 0)
{
lean_object* v___x_5081_; 
v___x_5081_ = lean_box(0);
return v___x_5081_;
}
else
{
lean_object* v_key_5082_; lean_object* v_value_5083_; lean_object* v_tail_5084_; size_t v___x_5085_; size_t v___x_5086_; uint8_t v___x_5087_; 
v_key_5082_ = lean_ctor_get(v_x_5080_, 0);
v_value_5083_ = lean_ctor_get(v_x_5080_, 1);
v_tail_5084_ = lean_ctor_get(v_x_5080_, 2);
v___x_5085_ = lean_ptr_addr(v_key_5082_);
v___x_5086_ = lean_ptr_addr(v_a_5079_);
v___x_5087_ = lean_usize_dec_eq(v___x_5085_, v___x_5086_);
if (v___x_5087_ == 0)
{
v_x_5080_ = v_tail_5084_;
goto _start;
}
else
{
lean_object* v___x_5089_; 
lean_inc(v_value_5083_);
v___x_5089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5089_, 0, v_value_5083_);
return v___x_5089_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_a_5090_, lean_object* v_x_5091_){
_start:
{
lean_object* v_res_5092_; 
v_res_5092_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___redArg(v_a_5090_, v_x_5091_);
lean_dec(v_x_5091_);
lean_dec_ref(v_a_5090_);
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___redArg(lean_object* v_m_5093_, lean_object* v_a_5094_){
_start:
{
lean_object* v_buckets_5095_; lean_object* v___x_5096_; size_t v___x_5097_; uint64_t v___x_5098_; uint64_t v___x_5099_; uint64_t v___x_5100_; uint64_t v___x_5101_; uint64_t v___x_5102_; uint64_t v_fold_5103_; uint64_t v___x_5104_; uint64_t v___x_5105_; uint64_t v___x_5106_; size_t v___x_5107_; size_t v___x_5108_; size_t v___x_5109_; size_t v___x_5110_; size_t v___x_5111_; lean_object* v___x_5112_; lean_object* v___x_5113_; 
v_buckets_5095_ = lean_ctor_get(v_m_5093_, 1);
v___x_5096_ = lean_array_get_size(v_buckets_5095_);
v___x_5097_ = lean_ptr_addr(v_a_5094_);
v___x_5098_ = lean_usize_to_uint64(v___x_5097_);
v___x_5099_ = 11ULL;
v___x_5100_ = lean_uint64_mix_hash(v___x_5098_, v___x_5099_);
v___x_5101_ = 32ULL;
v___x_5102_ = lean_uint64_shift_right(v___x_5100_, v___x_5101_);
v_fold_5103_ = lean_uint64_xor(v___x_5100_, v___x_5102_);
v___x_5104_ = 16ULL;
v___x_5105_ = lean_uint64_shift_right(v_fold_5103_, v___x_5104_);
v___x_5106_ = lean_uint64_xor(v_fold_5103_, v___x_5105_);
v___x_5107_ = lean_uint64_to_usize(v___x_5106_);
v___x_5108_ = lean_usize_of_nat(v___x_5096_);
v___x_5109_ = ((size_t)1ULL);
v___x_5110_ = lean_usize_sub(v___x_5108_, v___x_5109_);
v___x_5111_ = lean_usize_land(v___x_5107_, v___x_5110_);
v___x_5112_ = lean_array_uget_borrowed(v_buckets_5095_, v___x_5111_);
v___x_5113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___redArg(v_a_5094_, v___x_5112_);
return v___x_5113_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___redArg___boxed(lean_object* v_m_5114_, lean_object* v_a_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___redArg(v_m_5114_, v_a_5115_);
lean_dec_ref(v_a_5115_);
lean_dec_ref(v_m_5114_);
return v_res_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(lean_object* v_lctx_5117_, lean_object* v_params_5118_, lean_object* v_As_5119_, lean_object* v_e_5120_, lean_object* v_a_5121_, lean_object* v___y_5122_, lean_object* v___y_5123_){
_start:
{
lean_object* v_result_5125_; lean_object* v___y_5126_; lean_object* v___y_5127_; lean_object* v___x_5131_; 
v___x_5131_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___redArg(v_a_5121_, v_e_5120_);
if (lean_obj_tag(v___x_5131_) == 1)
{
lean_object* v_val_5132_; 
lean_dec_ref(v_e_5120_);
lean_dec_ref(v_lctx_5117_);
v_val_5132_ = lean_ctor_get(v___x_5131_, 0);
lean_inc(v_val_5132_);
lean_dec_ref(v___x_5131_);
v_result_5125_ = v_val_5132_;
v___y_5126_ = v_a_5121_;
v___y_5127_ = v___y_5123_;
goto v___jp_5124_;
}
else
{
lean_object* v___x_5133_; 
lean_dec(v___x_5131_);
lean_inc_ref(v_e_5120_);
lean_inc_ref(v_lctx_5117_);
v___x_5133_ = l_Lean4Lean_ElimNestedInductive_replaceIfNested(v_lctx_5117_, v_params_5118_, v_As_5119_, v_e_5120_, v___y_5122_, v___y_5123_);
if (lean_obj_tag(v___x_5133_) == 0)
{
lean_object* v_a_5134_; lean_object* v___x_5136_; uint8_t v_isShared_5137_; uint8_t v_isSharedCheck_5141_; 
lean_dec_ref(v_a_5121_);
lean_dec_ref(v_e_5120_);
lean_dec_ref(v_lctx_5117_);
v_a_5134_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5141_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5141_ == 0)
{
v___x_5136_ = v___x_5133_;
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
else
{
lean_inc(v_a_5134_);
lean_dec(v___x_5133_);
v___x_5136_ = lean_box(0);
v_isShared_5137_ = v_isSharedCheck_5141_;
goto v_resetjp_5135_;
}
v_resetjp_5135_:
{
lean_object* v___x_5139_; 
if (v_isShared_5137_ == 0)
{
v___x_5139_ = v___x_5136_;
goto v_reusejp_5138_;
}
else
{
lean_object* v_reuseFailAlloc_5140_; 
v_reuseFailAlloc_5140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5140_, 0, v_a_5134_);
v___x_5139_ = v_reuseFailAlloc_5140_;
goto v_reusejp_5138_;
}
v_reusejp_5138_:
{
return v___x_5139_;
}
}
}
else
{
lean_object* v_a_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5451_; 
v_a_5142_ = lean_ctor_get(v___x_5133_, 0);
v_isSharedCheck_5451_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5451_ == 0)
{
v___x_5144_ = v___x_5133_;
v_isShared_5145_ = v_isSharedCheck_5451_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_a_5142_);
lean_dec(v___x_5133_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5451_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v_fst_5146_; 
v_fst_5146_ = lean_ctor_get(v_a_5142_, 0);
if (lean_obj_tag(v_fst_5146_) == 0)
{
lean_del_object(v___x_5144_);
switch(lean_obj_tag(v_e_5120_))
{
case 7:
{
lean_object* v_snd_5147_; lean_object* v_binderName_5148_; lean_object* v_binderType_5149_; lean_object* v_body_5150_; uint8_t v_binderInfo_5151_; lean_object* v___x_5152_; 
v_snd_5147_ = lean_ctor_get(v_a_5142_, 1);
lean_inc(v_snd_5147_);
lean_dec(v_a_5142_);
v_binderName_5148_ = lean_ctor_get(v_e_5120_, 0);
v_binderType_5149_ = lean_ctor_get(v_e_5120_, 1);
v_body_5150_ = lean_ctor_get(v_e_5120_, 2);
v_binderInfo_5151_ = lean_ctor_get_uint8(v_e_5120_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_5149_);
lean_inc_ref(v_lctx_5117_);
v___x_5152_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_binderType_5149_, v_a_5121_, v___y_5122_, v_snd_5147_);
if (lean_obj_tag(v___x_5152_) == 0)
{
lean_dec_ref(v_e_5120_);
lean_dec_ref(v_lctx_5117_);
return v___x_5152_;
}
else
{
lean_object* v_a_5153_; lean_object* v_fst_5154_; lean_object* v_snd_5155_; lean_object* v_fst_5156_; lean_object* v_snd_5157_; lean_object* v___x_5158_; 
v_a_5153_ = lean_ctor_get(v___x_5152_, 0);
lean_inc(v_a_5153_);
lean_dec_ref(v___x_5152_);
v_fst_5154_ = lean_ctor_get(v_a_5153_, 0);
lean_inc(v_fst_5154_);
v_snd_5155_ = lean_ctor_get(v_a_5153_, 1);
lean_inc(v_snd_5155_);
lean_dec(v_a_5153_);
v_fst_5156_ = lean_ctor_get(v_fst_5154_, 0);
lean_inc(v_fst_5156_);
v_snd_5157_ = lean_ctor_get(v_fst_5154_, 1);
lean_inc(v_snd_5157_);
lean_dec(v_fst_5154_);
lean_inc_ref(v_body_5150_);
v___x_5158_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_body_5150_, v_snd_5157_, v___y_5122_, v_snd_5155_);
if (lean_obj_tag(v___x_5158_) == 0)
{
lean_dec(v_fst_5156_);
lean_dec_ref(v_e_5120_);
return v___x_5158_;
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5198_; 
v_a_5159_ = lean_ctor_get(v___x_5158_, 0);
v_isSharedCheck_5198_ = !lean_is_exclusive(v___x_5158_);
if (v_isSharedCheck_5198_ == 0)
{
v___x_5161_ = v___x_5158_;
v_isShared_5162_ = v_isSharedCheck_5198_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5158_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5198_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v_fst_5163_; lean_object* v_snd_5164_; lean_object* v___x_5166_; uint8_t v_isShared_5167_; uint8_t v_isSharedCheck_5197_; 
v_fst_5163_ = lean_ctor_get(v_a_5159_, 0);
v_snd_5164_ = lean_ctor_get(v_a_5159_, 1);
v_isSharedCheck_5197_ = !lean_is_exclusive(v_a_5159_);
if (v_isSharedCheck_5197_ == 0)
{
v___x_5166_ = v_a_5159_;
v_isShared_5167_ = v_isSharedCheck_5197_;
goto v_resetjp_5165_;
}
else
{
lean_inc(v_snd_5164_);
lean_inc(v_fst_5163_);
lean_dec(v_a_5159_);
v___x_5166_ = lean_box(0);
v_isShared_5167_ = v_isSharedCheck_5197_;
goto v_resetjp_5165_;
}
v_resetjp_5165_:
{
lean_object* v_fst_5168_; lean_object* v_snd_5169_; lean_object* v___x_5171_; uint8_t v_isShared_5172_; uint8_t v_isSharedCheck_5196_; 
v_fst_5168_ = lean_ctor_get(v_fst_5163_, 0);
v_snd_5169_ = lean_ctor_get(v_fst_5163_, 1);
v_isSharedCheck_5196_ = !lean_is_exclusive(v_fst_5163_);
if (v_isSharedCheck_5196_ == 0)
{
v___x_5171_ = v_fst_5163_;
v_isShared_5172_ = v_isSharedCheck_5196_;
goto v_resetjp_5170_;
}
else
{
lean_inc(v_snd_5169_);
lean_inc(v_fst_5168_);
lean_dec(v_fst_5163_);
v___x_5171_ = lean_box(0);
v_isShared_5172_ = v_isSharedCheck_5196_;
goto v_resetjp_5170_;
}
v_resetjp_5170_:
{
lean_object* v___y_5174_; uint8_t v___y_5186_; size_t v___x_5190_; size_t v___x_5191_; uint8_t v___x_5192_; 
v___x_5190_ = lean_ptr_addr(v_binderType_5149_);
v___x_5191_ = lean_ptr_addr(v_fst_5156_);
v___x_5192_ = lean_usize_dec_eq(v___x_5190_, v___x_5191_);
if (v___x_5192_ == 0)
{
v___y_5186_ = v___x_5192_;
goto v___jp_5185_;
}
else
{
size_t v___x_5193_; size_t v___x_5194_; uint8_t v___x_5195_; 
v___x_5193_ = lean_ptr_addr(v_body_5150_);
v___x_5194_ = lean_ptr_addr(v_fst_5168_);
v___x_5195_ = lean_usize_dec_eq(v___x_5193_, v___x_5194_);
v___y_5186_ = v___x_5195_;
goto v___jp_5185_;
}
v___jp_5173_:
{
lean_object* v___x_5175_; lean_object* v___x_5177_; 
lean_inc_ref(v___y_5174_);
v___x_5175_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_snd_5169_, v_e_5120_, v___y_5174_);
if (v_isShared_5172_ == 0)
{
lean_ctor_set(v___x_5171_, 1, v___x_5175_);
lean_ctor_set(v___x_5171_, 0, v___y_5174_);
v___x_5177_ = v___x_5171_;
goto v_reusejp_5176_;
}
else
{
lean_object* v_reuseFailAlloc_5184_; 
v_reuseFailAlloc_5184_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5184_, 0, v___y_5174_);
lean_ctor_set(v_reuseFailAlloc_5184_, 1, v___x_5175_);
v___x_5177_ = v_reuseFailAlloc_5184_;
goto v_reusejp_5176_;
}
v_reusejp_5176_:
{
lean_object* v___x_5179_; 
if (v_isShared_5167_ == 0)
{
lean_ctor_set(v___x_5166_, 0, v___x_5177_);
v___x_5179_ = v___x_5166_;
goto v_reusejp_5178_;
}
else
{
lean_object* v_reuseFailAlloc_5183_; 
v_reuseFailAlloc_5183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5183_, 0, v___x_5177_);
lean_ctor_set(v_reuseFailAlloc_5183_, 1, v_snd_5164_);
v___x_5179_ = v_reuseFailAlloc_5183_;
goto v_reusejp_5178_;
}
v_reusejp_5178_:
{
lean_object* v___x_5181_; 
if (v_isShared_5162_ == 0)
{
lean_ctor_set(v___x_5161_, 0, v___x_5179_);
v___x_5181_ = v___x_5161_;
goto v_reusejp_5180_;
}
else
{
lean_object* v_reuseFailAlloc_5182_; 
v_reuseFailAlloc_5182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5182_, 0, v___x_5179_);
v___x_5181_ = v_reuseFailAlloc_5182_;
goto v_reusejp_5180_;
}
v_reusejp_5180_:
{
return v___x_5181_;
}
}
}
}
v___jp_5185_:
{
if (v___y_5186_ == 0)
{
lean_object* v___x_5187_; 
lean_inc(v_binderName_5148_);
v___x_5187_ = l_Lean_Expr_forallE___override(v_binderName_5148_, v_fst_5156_, v_fst_5168_, v_binderInfo_5151_);
v___y_5174_ = v___x_5187_;
goto v___jp_5173_;
}
else
{
uint8_t v___x_5188_; 
v___x_5188_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5151_, v_binderInfo_5151_);
if (v___x_5188_ == 0)
{
lean_object* v___x_5189_; 
lean_inc(v_binderName_5148_);
v___x_5189_ = l_Lean_Expr_forallE___override(v_binderName_5148_, v_fst_5156_, v_fst_5168_, v_binderInfo_5151_);
v___y_5174_ = v___x_5189_;
goto v___jp_5173_;
}
else
{
lean_dec(v_fst_5168_);
lean_dec(v_fst_5156_);
lean_inc_ref(v_e_5120_);
v___y_5174_ = v_e_5120_;
goto v___jp_5173_;
}
}
}
}
}
}
}
}
}
case 6:
{
lean_object* v_snd_5199_; lean_object* v_binderName_5200_; lean_object* v_binderType_5201_; lean_object* v_body_5202_; uint8_t v_binderInfo_5203_; lean_object* v___x_5204_; 
v_snd_5199_ = lean_ctor_get(v_a_5142_, 1);
lean_inc(v_snd_5199_);
lean_dec(v_a_5142_);
v_binderName_5200_ = lean_ctor_get(v_e_5120_, 0);
v_binderType_5201_ = lean_ctor_get(v_e_5120_, 1);
v_body_5202_ = lean_ctor_get(v_e_5120_, 2);
v_binderInfo_5203_ = lean_ctor_get_uint8(v_e_5120_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_5201_);
lean_inc_ref(v_lctx_5117_);
v___x_5204_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_binderType_5201_, v_a_5121_, v___y_5122_, v_snd_5199_);
if (lean_obj_tag(v___x_5204_) == 0)
{
lean_dec_ref(v_e_5120_);
lean_dec_ref(v_lctx_5117_);
return v___x_5204_;
}
else
{
lean_object* v_a_5205_; lean_object* v_fst_5206_; lean_object* v_snd_5207_; lean_object* v_fst_5208_; lean_object* v_snd_5209_; lean_object* v___x_5210_; 
v_a_5205_ = lean_ctor_get(v___x_5204_, 0);
lean_inc(v_a_5205_);
lean_dec_ref(v___x_5204_);
v_fst_5206_ = lean_ctor_get(v_a_5205_, 0);
lean_inc(v_fst_5206_);
v_snd_5207_ = lean_ctor_get(v_a_5205_, 1);
lean_inc(v_snd_5207_);
lean_dec(v_a_5205_);
v_fst_5208_ = lean_ctor_get(v_fst_5206_, 0);
lean_inc(v_fst_5208_);
v_snd_5209_ = lean_ctor_get(v_fst_5206_, 1);
lean_inc(v_snd_5209_);
lean_dec(v_fst_5206_);
lean_inc_ref(v_body_5202_);
v___x_5210_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_body_5202_, v_snd_5209_, v___y_5122_, v_snd_5207_);
if (lean_obj_tag(v___x_5210_) == 0)
{
lean_dec(v_fst_5208_);
lean_dec_ref(v_e_5120_);
return v___x_5210_;
}
else
{
lean_object* v_a_5211_; lean_object* v___x_5213_; uint8_t v_isShared_5214_; uint8_t v_isSharedCheck_5250_; 
v_a_5211_ = lean_ctor_get(v___x_5210_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5210_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5213_ = v___x_5210_;
v_isShared_5214_ = v_isSharedCheck_5250_;
goto v_resetjp_5212_;
}
else
{
lean_inc(v_a_5211_);
lean_dec(v___x_5210_);
v___x_5213_ = lean_box(0);
v_isShared_5214_ = v_isSharedCheck_5250_;
goto v_resetjp_5212_;
}
v_resetjp_5212_:
{
lean_object* v_fst_5215_; lean_object* v_snd_5216_; lean_object* v___x_5218_; uint8_t v_isShared_5219_; uint8_t v_isSharedCheck_5249_; 
v_fst_5215_ = lean_ctor_get(v_a_5211_, 0);
v_snd_5216_ = lean_ctor_get(v_a_5211_, 1);
v_isSharedCheck_5249_ = !lean_is_exclusive(v_a_5211_);
if (v_isSharedCheck_5249_ == 0)
{
v___x_5218_ = v_a_5211_;
v_isShared_5219_ = v_isSharedCheck_5249_;
goto v_resetjp_5217_;
}
else
{
lean_inc(v_snd_5216_);
lean_inc(v_fst_5215_);
lean_dec(v_a_5211_);
v___x_5218_ = lean_box(0);
v_isShared_5219_ = v_isSharedCheck_5249_;
goto v_resetjp_5217_;
}
v_resetjp_5217_:
{
lean_object* v_fst_5220_; lean_object* v_snd_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5248_; 
v_fst_5220_ = lean_ctor_get(v_fst_5215_, 0);
v_snd_5221_ = lean_ctor_get(v_fst_5215_, 1);
v_isSharedCheck_5248_ = !lean_is_exclusive(v_fst_5215_);
if (v_isSharedCheck_5248_ == 0)
{
v___x_5223_ = v_fst_5215_;
v_isShared_5224_ = v_isSharedCheck_5248_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_snd_5221_);
lean_inc(v_fst_5220_);
lean_dec(v_fst_5215_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5248_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___y_5226_; uint8_t v___y_5238_; size_t v___x_5242_; size_t v___x_5243_; uint8_t v___x_5244_; 
v___x_5242_ = lean_ptr_addr(v_binderType_5201_);
v___x_5243_ = lean_ptr_addr(v_fst_5208_);
v___x_5244_ = lean_usize_dec_eq(v___x_5242_, v___x_5243_);
if (v___x_5244_ == 0)
{
v___y_5238_ = v___x_5244_;
goto v___jp_5237_;
}
else
{
size_t v___x_5245_; size_t v___x_5246_; uint8_t v___x_5247_; 
v___x_5245_ = lean_ptr_addr(v_body_5202_);
v___x_5246_ = lean_ptr_addr(v_fst_5220_);
v___x_5247_ = lean_usize_dec_eq(v___x_5245_, v___x_5246_);
v___y_5238_ = v___x_5247_;
goto v___jp_5237_;
}
v___jp_5225_:
{
lean_object* v___x_5227_; lean_object* v___x_5229_; 
lean_inc_ref(v___y_5226_);
v___x_5227_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_snd_5221_, v_e_5120_, v___y_5226_);
if (v_isShared_5224_ == 0)
{
lean_ctor_set(v___x_5223_, 1, v___x_5227_);
lean_ctor_set(v___x_5223_, 0, v___y_5226_);
v___x_5229_ = v___x_5223_;
goto v_reusejp_5228_;
}
else
{
lean_object* v_reuseFailAlloc_5236_; 
v_reuseFailAlloc_5236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5236_, 0, v___y_5226_);
lean_ctor_set(v_reuseFailAlloc_5236_, 1, v___x_5227_);
v___x_5229_ = v_reuseFailAlloc_5236_;
goto v_reusejp_5228_;
}
v_reusejp_5228_:
{
lean_object* v___x_5231_; 
if (v_isShared_5219_ == 0)
{
lean_ctor_set(v___x_5218_, 0, v___x_5229_);
v___x_5231_ = v___x_5218_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5235_; 
v_reuseFailAlloc_5235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5235_, 0, v___x_5229_);
lean_ctor_set(v_reuseFailAlloc_5235_, 1, v_snd_5216_);
v___x_5231_ = v_reuseFailAlloc_5235_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
lean_object* v___x_5233_; 
if (v_isShared_5214_ == 0)
{
lean_ctor_set(v___x_5213_, 0, v___x_5231_);
v___x_5233_ = v___x_5213_;
goto v_reusejp_5232_;
}
else
{
lean_object* v_reuseFailAlloc_5234_; 
v_reuseFailAlloc_5234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
v___x_5233_ = v_reuseFailAlloc_5234_;
goto v_reusejp_5232_;
}
v_reusejp_5232_:
{
return v___x_5233_;
}
}
}
}
v___jp_5237_:
{
if (v___y_5238_ == 0)
{
lean_object* v___x_5239_; 
lean_inc(v_binderName_5200_);
v___x_5239_ = l_Lean_Expr_lam___override(v_binderName_5200_, v_fst_5208_, v_fst_5220_, v_binderInfo_5203_);
v___y_5226_ = v___x_5239_;
goto v___jp_5225_;
}
else
{
uint8_t v___x_5240_; 
v___x_5240_ = l_Lean_instBEqBinderInfo_beq(v_binderInfo_5203_, v_binderInfo_5203_);
if (v___x_5240_ == 0)
{
lean_object* v___x_5241_; 
lean_inc(v_binderName_5200_);
v___x_5241_ = l_Lean_Expr_lam___override(v_binderName_5200_, v_fst_5208_, v_fst_5220_, v_binderInfo_5203_);
v___y_5226_ = v___x_5241_;
goto v___jp_5225_;
}
else
{
lean_dec(v_fst_5220_);
lean_dec(v_fst_5208_);
lean_inc_ref(v_e_5120_);
v___y_5226_ = v_e_5120_;
goto v___jp_5225_;
}
}
}
}
}
}
}
}
}
case 10:
{
lean_object* v_snd_5251_; lean_object* v_data_5252_; lean_object* v_expr_5253_; lean_object* v___x_5254_; 
v_snd_5251_ = lean_ctor_get(v_a_5142_, 1);
lean_inc(v_snd_5251_);
lean_dec(v_a_5142_);
v_data_5252_ = lean_ctor_get(v_e_5120_, 0);
v_expr_5253_ = lean_ctor_get(v_e_5120_, 1);
lean_inc_ref(v_expr_5253_);
v___x_5254_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_expr_5253_, v_a_5121_, v___y_5122_, v_snd_5251_);
if (lean_obj_tag(v___x_5254_) == 0)
{
lean_dec_ref(v_e_5120_);
return v___x_5254_;
}
else
{
lean_object* v_a_5255_; lean_object* v___x_5257_; uint8_t v_isShared_5258_; uint8_t v_isSharedCheck_5287_; 
v_a_5255_ = lean_ctor_get(v___x_5254_, 0);
v_isSharedCheck_5287_ = !lean_is_exclusive(v___x_5254_);
if (v_isSharedCheck_5287_ == 0)
{
v___x_5257_ = v___x_5254_;
v_isShared_5258_ = v_isSharedCheck_5287_;
goto v_resetjp_5256_;
}
else
{
lean_inc(v_a_5255_);
lean_dec(v___x_5254_);
v___x_5257_ = lean_box(0);
v_isShared_5258_ = v_isSharedCheck_5287_;
goto v_resetjp_5256_;
}
v_resetjp_5256_:
{
lean_object* v_fst_5259_; lean_object* v_snd_5260_; lean_object* v___x_5262_; uint8_t v_isShared_5263_; uint8_t v_isSharedCheck_5286_; 
v_fst_5259_ = lean_ctor_get(v_a_5255_, 0);
v_snd_5260_ = lean_ctor_get(v_a_5255_, 1);
v_isSharedCheck_5286_ = !lean_is_exclusive(v_a_5255_);
if (v_isSharedCheck_5286_ == 0)
{
v___x_5262_ = v_a_5255_;
v_isShared_5263_ = v_isSharedCheck_5286_;
goto v_resetjp_5261_;
}
else
{
lean_inc(v_snd_5260_);
lean_inc(v_fst_5259_);
lean_dec(v_a_5255_);
v___x_5262_ = lean_box(0);
v_isShared_5263_ = v_isSharedCheck_5286_;
goto v_resetjp_5261_;
}
v_resetjp_5261_:
{
lean_object* v_fst_5264_; lean_object* v_snd_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5285_; 
v_fst_5264_ = lean_ctor_get(v_fst_5259_, 0);
v_snd_5265_ = lean_ctor_get(v_fst_5259_, 1);
v_isSharedCheck_5285_ = !lean_is_exclusive(v_fst_5259_);
if (v_isSharedCheck_5285_ == 0)
{
v___x_5267_ = v_fst_5259_;
v_isShared_5268_ = v_isSharedCheck_5285_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_snd_5265_);
lean_inc(v_fst_5264_);
lean_dec(v_fst_5259_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5285_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
lean_object* v___y_5270_; size_t v___x_5281_; size_t v___x_5282_; uint8_t v___x_5283_; 
v___x_5281_ = lean_ptr_addr(v_expr_5253_);
v___x_5282_ = lean_ptr_addr(v_fst_5264_);
v___x_5283_ = lean_usize_dec_eq(v___x_5281_, v___x_5282_);
if (v___x_5283_ == 0)
{
lean_object* v___x_5284_; 
lean_inc(v_data_5252_);
v___x_5284_ = l_Lean_Expr_mdata___override(v_data_5252_, v_fst_5264_);
v___y_5270_ = v___x_5284_;
goto v___jp_5269_;
}
else
{
lean_dec(v_fst_5264_);
lean_inc_ref(v_e_5120_);
v___y_5270_ = v_e_5120_;
goto v___jp_5269_;
}
v___jp_5269_:
{
lean_object* v___x_5271_; lean_object* v___x_5273_; 
lean_inc_ref(v___y_5270_);
v___x_5271_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_snd_5265_, v_e_5120_, v___y_5270_);
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 1, v___x_5271_);
lean_ctor_set(v___x_5267_, 0, v___y_5270_);
v___x_5273_ = v___x_5267_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5280_; 
v_reuseFailAlloc_5280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5280_, 0, v___y_5270_);
lean_ctor_set(v_reuseFailAlloc_5280_, 1, v___x_5271_);
v___x_5273_ = v_reuseFailAlloc_5280_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
lean_object* v___x_5275_; 
if (v_isShared_5263_ == 0)
{
lean_ctor_set(v___x_5262_, 0, v___x_5273_);
v___x_5275_ = v___x_5262_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5279_; 
v_reuseFailAlloc_5279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5279_, 0, v___x_5273_);
lean_ctor_set(v_reuseFailAlloc_5279_, 1, v_snd_5260_);
v___x_5275_ = v_reuseFailAlloc_5279_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5277_; 
if (v_isShared_5258_ == 0)
{
lean_ctor_set(v___x_5257_, 0, v___x_5275_);
v___x_5277_ = v___x_5257_;
goto v_reusejp_5276_;
}
else
{
lean_object* v_reuseFailAlloc_5278_; 
v_reuseFailAlloc_5278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5278_, 0, v___x_5275_);
v___x_5277_ = v_reuseFailAlloc_5278_;
goto v_reusejp_5276_;
}
v_reusejp_5276_:
{
return v___x_5277_;
}
}
}
}
}
}
}
}
}
case 8:
{
lean_object* v_snd_5288_; lean_object* v_declName_5289_; lean_object* v_type_5290_; lean_object* v_value_5291_; lean_object* v_body_5292_; uint8_t v_nondep_5293_; lean_object* v___x_5294_; 
v_snd_5288_ = lean_ctor_get(v_a_5142_, 1);
lean_inc(v_snd_5288_);
lean_dec(v_a_5142_);
v_declName_5289_ = lean_ctor_get(v_e_5120_, 0);
v_type_5290_ = lean_ctor_get(v_e_5120_, 1);
v_value_5291_ = lean_ctor_get(v_e_5120_, 2);
v_body_5292_ = lean_ctor_get(v_e_5120_, 3);
v_nondep_5293_ = lean_ctor_get_uint8(v_e_5120_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_5290_);
lean_inc_ref(v_lctx_5117_);
v___x_5294_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_type_5290_, v_a_5121_, v___y_5122_, v_snd_5288_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_dec_ref(v_e_5120_);
lean_dec_ref(v_lctx_5117_);
return v___x_5294_;
}
else
{
lean_object* v_a_5295_; lean_object* v_fst_5296_; lean_object* v_snd_5297_; lean_object* v_fst_5298_; lean_object* v_snd_5299_; lean_object* v___x_5300_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref(v___x_5294_);
v_fst_5296_ = lean_ctor_get(v_a_5295_, 0);
lean_inc(v_fst_5296_);
v_snd_5297_ = lean_ctor_get(v_a_5295_, 1);
lean_inc(v_snd_5297_);
lean_dec(v_a_5295_);
v_fst_5298_ = lean_ctor_get(v_fst_5296_, 0);
lean_inc(v_fst_5298_);
v_snd_5299_ = lean_ctor_get(v_fst_5296_, 1);
lean_inc(v_snd_5299_);
lean_dec(v_fst_5296_);
lean_inc_ref(v_value_5291_);
lean_inc_ref(v_lctx_5117_);
v___x_5300_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_value_5291_, v_snd_5299_, v___y_5122_, v_snd_5297_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_dec(v_fst_5298_);
lean_dec_ref(v_e_5120_);
lean_dec_ref(v_lctx_5117_);
return v___x_5300_;
}
else
{
lean_object* v_a_5301_; lean_object* v_fst_5302_; lean_object* v_snd_5303_; lean_object* v_fst_5304_; lean_object* v_snd_5305_; lean_object* v___x_5306_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5301_);
lean_dec_ref(v___x_5300_);
v_fst_5302_ = lean_ctor_get(v_a_5301_, 0);
lean_inc(v_fst_5302_);
v_snd_5303_ = lean_ctor_get(v_a_5301_, 1);
lean_inc(v_snd_5303_);
lean_dec(v_a_5301_);
v_fst_5304_ = lean_ctor_get(v_fst_5302_, 0);
lean_inc(v_fst_5304_);
v_snd_5305_ = lean_ctor_get(v_fst_5302_, 1);
lean_inc(v_snd_5305_);
lean_dec(v_fst_5302_);
lean_inc_ref(v_body_5292_);
v___x_5306_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_body_5292_, v_snd_5305_, v___y_5122_, v_snd_5303_);
if (lean_obj_tag(v___x_5306_) == 0)
{
lean_dec(v_fst_5304_);
lean_dec(v_fst_5298_);
lean_dec_ref(v_e_5120_);
return v___x_5306_;
}
else
{
lean_object* v_a_5307_; lean_object* v___x_5309_; uint8_t v_isShared_5310_; uint8_t v_isSharedCheck_5348_; 
v_a_5307_ = lean_ctor_get(v___x_5306_, 0);
v_isSharedCheck_5348_ = !lean_is_exclusive(v___x_5306_);
if (v_isSharedCheck_5348_ == 0)
{
v___x_5309_ = v___x_5306_;
v_isShared_5310_ = v_isSharedCheck_5348_;
goto v_resetjp_5308_;
}
else
{
lean_inc(v_a_5307_);
lean_dec(v___x_5306_);
v___x_5309_ = lean_box(0);
v_isShared_5310_ = v_isSharedCheck_5348_;
goto v_resetjp_5308_;
}
v_resetjp_5308_:
{
lean_object* v_fst_5311_; lean_object* v_snd_5312_; lean_object* v___x_5314_; uint8_t v_isShared_5315_; uint8_t v_isSharedCheck_5347_; 
v_fst_5311_ = lean_ctor_get(v_a_5307_, 0);
v_snd_5312_ = lean_ctor_get(v_a_5307_, 1);
v_isSharedCheck_5347_ = !lean_is_exclusive(v_a_5307_);
if (v_isSharedCheck_5347_ == 0)
{
v___x_5314_ = v_a_5307_;
v_isShared_5315_ = v_isSharedCheck_5347_;
goto v_resetjp_5313_;
}
else
{
lean_inc(v_snd_5312_);
lean_inc(v_fst_5311_);
lean_dec(v_a_5307_);
v___x_5314_ = lean_box(0);
v_isShared_5315_ = v_isSharedCheck_5347_;
goto v_resetjp_5313_;
}
v_resetjp_5313_:
{
lean_object* v_fst_5316_; lean_object* v_snd_5317_; lean_object* v___x_5319_; uint8_t v_isShared_5320_; uint8_t v_isSharedCheck_5346_; 
v_fst_5316_ = lean_ctor_get(v_fst_5311_, 0);
v_snd_5317_ = lean_ctor_get(v_fst_5311_, 1);
v_isSharedCheck_5346_ = !lean_is_exclusive(v_fst_5311_);
if (v_isSharedCheck_5346_ == 0)
{
v___x_5319_ = v_fst_5311_;
v_isShared_5320_ = v_isSharedCheck_5346_;
goto v_resetjp_5318_;
}
else
{
lean_inc(v_snd_5317_);
lean_inc(v_fst_5316_);
lean_dec(v_fst_5311_);
v___x_5319_ = lean_box(0);
v_isShared_5320_ = v_isSharedCheck_5346_;
goto v_resetjp_5318_;
}
v_resetjp_5318_:
{
lean_object* v___y_5322_; uint8_t v___y_5334_; size_t v___x_5340_; size_t v___x_5341_; uint8_t v___x_5342_; 
v___x_5340_ = lean_ptr_addr(v_type_5290_);
v___x_5341_ = lean_ptr_addr(v_fst_5298_);
v___x_5342_ = lean_usize_dec_eq(v___x_5340_, v___x_5341_);
if (v___x_5342_ == 0)
{
v___y_5334_ = v___x_5342_;
goto v___jp_5333_;
}
else
{
size_t v___x_5343_; size_t v___x_5344_; uint8_t v___x_5345_; 
v___x_5343_ = lean_ptr_addr(v_value_5291_);
v___x_5344_ = lean_ptr_addr(v_fst_5304_);
v___x_5345_ = lean_usize_dec_eq(v___x_5343_, v___x_5344_);
v___y_5334_ = v___x_5345_;
goto v___jp_5333_;
}
v___jp_5321_:
{
lean_object* v___x_5323_; lean_object* v___x_5325_; 
lean_inc_ref(v___y_5322_);
v___x_5323_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_snd_5317_, v_e_5120_, v___y_5322_);
if (v_isShared_5320_ == 0)
{
lean_ctor_set(v___x_5319_, 1, v___x_5323_);
lean_ctor_set(v___x_5319_, 0, v___y_5322_);
v___x_5325_ = v___x_5319_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v___y_5322_);
lean_ctor_set(v_reuseFailAlloc_5332_, 1, v___x_5323_);
v___x_5325_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
lean_object* v___x_5327_; 
if (v_isShared_5315_ == 0)
{
lean_ctor_set(v___x_5314_, 0, v___x_5325_);
v___x_5327_ = v___x_5314_;
goto v_reusejp_5326_;
}
else
{
lean_object* v_reuseFailAlloc_5331_; 
v_reuseFailAlloc_5331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5331_, 0, v___x_5325_);
lean_ctor_set(v_reuseFailAlloc_5331_, 1, v_snd_5312_);
v___x_5327_ = v_reuseFailAlloc_5331_;
goto v_reusejp_5326_;
}
v_reusejp_5326_:
{
lean_object* v___x_5329_; 
if (v_isShared_5310_ == 0)
{
lean_ctor_set(v___x_5309_, 0, v___x_5327_);
v___x_5329_ = v___x_5309_;
goto v_reusejp_5328_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v___x_5327_);
v___x_5329_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5328_;
}
v_reusejp_5328_:
{
return v___x_5329_;
}
}
}
}
v___jp_5333_:
{
if (v___y_5334_ == 0)
{
lean_object* v___x_5335_; 
lean_inc(v_declName_5289_);
v___x_5335_ = l_Lean_Expr_letE___override(v_declName_5289_, v_fst_5298_, v_fst_5304_, v_fst_5316_, v_nondep_5293_);
v___y_5322_ = v___x_5335_;
goto v___jp_5321_;
}
else
{
size_t v___x_5336_; size_t v___x_5337_; uint8_t v___x_5338_; 
v___x_5336_ = lean_ptr_addr(v_body_5292_);
v___x_5337_ = lean_ptr_addr(v_fst_5316_);
v___x_5338_ = lean_usize_dec_eq(v___x_5336_, v___x_5337_);
if (v___x_5338_ == 0)
{
lean_object* v___x_5339_; 
lean_inc(v_declName_5289_);
v___x_5339_ = l_Lean_Expr_letE___override(v_declName_5289_, v_fst_5298_, v_fst_5304_, v_fst_5316_, v_nondep_5293_);
v___y_5322_ = v___x_5339_;
goto v___jp_5321_;
}
else
{
lean_dec(v_fst_5316_);
lean_dec(v_fst_5304_);
lean_dec(v_fst_5298_);
lean_inc_ref(v_e_5120_);
v___y_5322_ = v_e_5120_;
goto v___jp_5321_;
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
case 5:
{
lean_object* v_snd_5349_; lean_object* v_fn_5350_; lean_object* v_arg_5351_; lean_object* v___x_5352_; 
v_snd_5349_ = lean_ctor_get(v_a_5142_, 1);
lean_inc(v_snd_5349_);
lean_dec(v_a_5142_);
v_fn_5350_ = lean_ctor_get(v_e_5120_, 0);
v_arg_5351_ = lean_ctor_get(v_e_5120_, 1);
lean_inc_ref(v_fn_5350_);
lean_inc_ref(v_lctx_5117_);
v___x_5352_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_fn_5350_, v_a_5121_, v___y_5122_, v_snd_5349_);
if (lean_obj_tag(v___x_5352_) == 0)
{
lean_dec_ref(v_e_5120_);
lean_dec_ref(v_lctx_5117_);
return v___x_5352_;
}
else
{
lean_object* v_a_5353_; lean_object* v_fst_5354_; lean_object* v_snd_5355_; lean_object* v_fst_5356_; lean_object* v_snd_5357_; lean_object* v___x_5358_; 
v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
lean_inc(v_a_5353_);
lean_dec_ref(v___x_5352_);
v_fst_5354_ = lean_ctor_get(v_a_5353_, 0);
lean_inc(v_fst_5354_);
v_snd_5355_ = lean_ctor_get(v_a_5353_, 1);
lean_inc(v_snd_5355_);
lean_dec(v_a_5353_);
v_fst_5356_ = lean_ctor_get(v_fst_5354_, 0);
lean_inc(v_fst_5356_);
v_snd_5357_ = lean_ctor_get(v_fst_5354_, 1);
lean_inc(v_snd_5357_);
lean_dec(v_fst_5354_);
lean_inc_ref(v_arg_5351_);
v___x_5358_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_arg_5351_, v_snd_5357_, v___y_5122_, v_snd_5355_);
if (lean_obj_tag(v___x_5358_) == 0)
{
lean_dec(v_fst_5356_);
lean_dec_ref(v_e_5120_);
return v___x_5358_;
}
else
{
lean_object* v_a_5359_; lean_object* v___x_5361_; uint8_t v_isShared_5362_; uint8_t v_isSharedCheck_5396_; 
v_a_5359_ = lean_ctor_get(v___x_5358_, 0);
v_isSharedCheck_5396_ = !lean_is_exclusive(v___x_5358_);
if (v_isSharedCheck_5396_ == 0)
{
v___x_5361_ = v___x_5358_;
v_isShared_5362_ = v_isSharedCheck_5396_;
goto v_resetjp_5360_;
}
else
{
lean_inc(v_a_5359_);
lean_dec(v___x_5358_);
v___x_5361_ = lean_box(0);
v_isShared_5362_ = v_isSharedCheck_5396_;
goto v_resetjp_5360_;
}
v_resetjp_5360_:
{
lean_object* v_fst_5363_; lean_object* v_snd_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5395_; 
v_fst_5363_ = lean_ctor_get(v_a_5359_, 0);
v_snd_5364_ = lean_ctor_get(v_a_5359_, 1);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_a_5359_);
if (v_isSharedCheck_5395_ == 0)
{
v___x_5366_ = v_a_5359_;
v_isShared_5367_ = v_isSharedCheck_5395_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_snd_5364_);
lean_inc(v_fst_5363_);
lean_dec(v_a_5359_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5395_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v_fst_5368_; lean_object* v_snd_5369_; lean_object* v___x_5371_; uint8_t v_isShared_5372_; uint8_t v_isSharedCheck_5394_; 
v_fst_5368_ = lean_ctor_get(v_fst_5363_, 0);
v_snd_5369_ = lean_ctor_get(v_fst_5363_, 1);
v_isSharedCheck_5394_ = !lean_is_exclusive(v_fst_5363_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5371_ = v_fst_5363_;
v_isShared_5372_ = v_isSharedCheck_5394_;
goto v_resetjp_5370_;
}
else
{
lean_inc(v_snd_5369_);
lean_inc(v_fst_5368_);
lean_dec(v_fst_5363_);
v___x_5371_ = lean_box(0);
v_isShared_5372_ = v_isSharedCheck_5394_;
goto v_resetjp_5370_;
}
v_resetjp_5370_:
{
lean_object* v___y_5374_; uint8_t v___y_5386_; size_t v___x_5388_; size_t v___x_5389_; uint8_t v___x_5390_; 
v___x_5388_ = lean_ptr_addr(v_fn_5350_);
v___x_5389_ = lean_ptr_addr(v_fst_5356_);
v___x_5390_ = lean_usize_dec_eq(v___x_5388_, v___x_5389_);
if (v___x_5390_ == 0)
{
v___y_5386_ = v___x_5390_;
goto v___jp_5385_;
}
else
{
size_t v___x_5391_; size_t v___x_5392_; uint8_t v___x_5393_; 
v___x_5391_ = lean_ptr_addr(v_arg_5351_);
v___x_5392_ = lean_ptr_addr(v_fst_5368_);
v___x_5393_ = lean_usize_dec_eq(v___x_5391_, v___x_5392_);
v___y_5386_ = v___x_5393_;
goto v___jp_5385_;
}
v___jp_5373_:
{
lean_object* v___x_5375_; lean_object* v___x_5377_; 
lean_inc_ref(v___y_5374_);
v___x_5375_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_snd_5369_, v_e_5120_, v___y_5374_);
if (v_isShared_5372_ == 0)
{
lean_ctor_set(v___x_5371_, 1, v___x_5375_);
lean_ctor_set(v___x_5371_, 0, v___y_5374_);
v___x_5377_ = v___x_5371_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5384_; 
v_reuseFailAlloc_5384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5384_, 0, v___y_5374_);
lean_ctor_set(v_reuseFailAlloc_5384_, 1, v___x_5375_);
v___x_5377_ = v_reuseFailAlloc_5384_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
lean_object* v___x_5379_; 
if (v_isShared_5367_ == 0)
{
lean_ctor_set(v___x_5366_, 0, v___x_5377_);
v___x_5379_ = v___x_5366_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5377_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v_snd_5364_);
v___x_5379_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
lean_object* v___x_5381_; 
if (v_isShared_5362_ == 0)
{
lean_ctor_set(v___x_5361_, 0, v___x_5379_);
v___x_5381_ = v___x_5361_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5379_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
v___jp_5385_:
{
if (v___y_5386_ == 0)
{
lean_object* v___x_5387_; 
v___x_5387_ = l_Lean_Expr_app___override(v_fst_5356_, v_fst_5368_);
v___y_5374_ = v___x_5387_;
goto v___jp_5373_;
}
else
{
lean_dec(v_fst_5368_);
lean_dec(v_fst_5356_);
lean_inc_ref(v_e_5120_);
v___y_5374_ = v_e_5120_;
goto v___jp_5373_;
}
}
}
}
}
}
}
}
case 11:
{
lean_object* v_snd_5397_; lean_object* v_typeName_5398_; lean_object* v_idx_5399_; lean_object* v_struct_5400_; lean_object* v___x_5401_; 
v_snd_5397_ = lean_ctor_get(v_a_5142_, 1);
lean_inc(v_snd_5397_);
lean_dec(v_a_5142_);
v_typeName_5398_ = lean_ctor_get(v_e_5120_, 0);
v_idx_5399_ = lean_ctor_get(v_e_5120_, 1);
v_struct_5400_ = lean_ctor_get(v_e_5120_, 2);
lean_inc_ref(v_struct_5400_);
v___x_5401_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5117_, v_params_5118_, v_As_5119_, v_struct_5400_, v_a_5121_, v___y_5122_, v_snd_5397_);
if (lean_obj_tag(v___x_5401_) == 0)
{
lean_dec_ref(v_e_5120_);
return v___x_5401_;
}
else
{
lean_object* v_a_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5434_; 
v_a_5402_ = lean_ctor_get(v___x_5401_, 0);
v_isSharedCheck_5434_ = !lean_is_exclusive(v___x_5401_);
if (v_isSharedCheck_5434_ == 0)
{
v___x_5404_ = v___x_5401_;
v_isShared_5405_ = v_isSharedCheck_5434_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_a_5402_);
lean_dec(v___x_5401_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5434_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v_fst_5406_; lean_object* v_snd_5407_; lean_object* v___x_5409_; uint8_t v_isShared_5410_; uint8_t v_isSharedCheck_5433_; 
v_fst_5406_ = lean_ctor_get(v_a_5402_, 0);
v_snd_5407_ = lean_ctor_get(v_a_5402_, 1);
v_isSharedCheck_5433_ = !lean_is_exclusive(v_a_5402_);
if (v_isSharedCheck_5433_ == 0)
{
v___x_5409_ = v_a_5402_;
v_isShared_5410_ = v_isSharedCheck_5433_;
goto v_resetjp_5408_;
}
else
{
lean_inc(v_snd_5407_);
lean_inc(v_fst_5406_);
lean_dec(v_a_5402_);
v___x_5409_ = lean_box(0);
v_isShared_5410_ = v_isSharedCheck_5433_;
goto v_resetjp_5408_;
}
v_resetjp_5408_:
{
lean_object* v_fst_5411_; lean_object* v_snd_5412_; lean_object* v___x_5414_; uint8_t v_isShared_5415_; uint8_t v_isSharedCheck_5432_; 
v_fst_5411_ = lean_ctor_get(v_fst_5406_, 0);
v_snd_5412_ = lean_ctor_get(v_fst_5406_, 1);
v_isSharedCheck_5432_ = !lean_is_exclusive(v_fst_5406_);
if (v_isSharedCheck_5432_ == 0)
{
v___x_5414_ = v_fst_5406_;
v_isShared_5415_ = v_isSharedCheck_5432_;
goto v_resetjp_5413_;
}
else
{
lean_inc(v_snd_5412_);
lean_inc(v_fst_5411_);
lean_dec(v_fst_5406_);
v___x_5414_ = lean_box(0);
v_isShared_5415_ = v_isSharedCheck_5432_;
goto v_resetjp_5413_;
}
v_resetjp_5413_:
{
lean_object* v___y_5417_; size_t v___x_5428_; size_t v___x_5429_; uint8_t v___x_5430_; 
v___x_5428_ = lean_ptr_addr(v_struct_5400_);
v___x_5429_ = lean_ptr_addr(v_fst_5411_);
v___x_5430_ = lean_usize_dec_eq(v___x_5428_, v___x_5429_);
if (v___x_5430_ == 0)
{
lean_object* v___x_5431_; 
lean_inc(v_idx_5399_);
lean_inc(v_typeName_5398_);
v___x_5431_ = l_Lean_Expr_proj___override(v_typeName_5398_, v_idx_5399_, v_fst_5411_);
v___y_5417_ = v___x_5431_;
goto v___jp_5416_;
}
else
{
lean_dec(v_fst_5411_);
lean_inc_ref(v_e_5120_);
v___y_5417_ = v_e_5120_;
goto v___jp_5416_;
}
v___jp_5416_:
{
lean_object* v___x_5418_; lean_object* v___x_5420_; 
lean_inc_ref(v___y_5417_);
v___x_5418_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_snd_5412_, v_e_5120_, v___y_5417_);
if (v_isShared_5415_ == 0)
{
lean_ctor_set(v___x_5414_, 1, v___x_5418_);
lean_ctor_set(v___x_5414_, 0, v___y_5417_);
v___x_5420_ = v___x_5414_;
goto v_reusejp_5419_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___y_5417_);
lean_ctor_set(v_reuseFailAlloc_5427_, 1, v___x_5418_);
v___x_5420_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5419_;
}
v_reusejp_5419_:
{
lean_object* v___x_5422_; 
if (v_isShared_5410_ == 0)
{
lean_ctor_set(v___x_5409_, 0, v___x_5420_);
v___x_5422_ = v___x_5409_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5420_);
lean_ctor_set(v_reuseFailAlloc_5426_, 1, v_snd_5407_);
v___x_5422_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
lean_object* v___x_5424_; 
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 0, v___x_5422_);
v___x_5424_ = v___x_5404_;
goto v_reusejp_5423_;
}
else
{
lean_object* v_reuseFailAlloc_5425_; 
v_reuseFailAlloc_5425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5425_, 0, v___x_5422_);
v___x_5424_ = v_reuseFailAlloc_5425_;
goto v_reusejp_5423_;
}
v_reusejp_5423_:
{
return v___x_5424_;
}
}
}
}
}
}
}
}
}
default: 
{
lean_object* v_snd_5435_; 
lean_dec_ref(v_lctx_5117_);
v_snd_5435_ = lean_ctor_get(v_a_5142_, 1);
lean_inc(v_snd_5435_);
lean_dec(v_a_5142_);
v_result_5125_ = v_e_5120_;
v___y_5126_ = v_a_5121_;
v___y_5127_ = v_snd_5435_;
goto v___jp_5124_;
}
}
}
else
{
lean_object* v_snd_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5449_; 
lean_inc_ref(v_fst_5146_);
lean_dec_ref(v_lctx_5117_);
v_snd_5436_ = lean_ctor_get(v_a_5142_, 1);
v_isSharedCheck_5449_ = !lean_is_exclusive(v_a_5142_);
if (v_isSharedCheck_5449_ == 0)
{
lean_object* v_unused_5450_; 
v_unused_5450_ = lean_ctor_get(v_a_5142_, 0);
lean_dec(v_unused_5450_);
v___x_5438_ = v_a_5142_;
v_isShared_5439_ = v_isSharedCheck_5449_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_snd_5436_);
lean_dec(v_a_5142_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5449_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
lean_object* v_val_5440_; lean_object* v___x_5441_; lean_object* v___x_5443_; 
v_val_5440_ = lean_ctor_get(v_fst_5146_, 0);
lean_inc_n(v_val_5440_, 2);
lean_dec_ref(v_fst_5146_);
v___x_5441_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_a_5121_, v_e_5120_, v_val_5440_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 1, v___x_5441_);
lean_ctor_set(v___x_5438_, 0, v_val_5440_);
v___x_5443_ = v___x_5438_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_val_5440_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v___x_5441_);
v___x_5443_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
lean_object* v___x_5444_; lean_object* v___x_5446_; 
v___x_5444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5444_, 0, v___x_5443_);
lean_ctor_set(v___x_5444_, 1, v_snd_5436_);
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 0, v___x_5444_);
v___x_5446_ = v___x_5144_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v___x_5444_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
}
}
}
}
v___jp_5124_:
{
lean_object* v___x_5128_; lean_object* v___x_5129_; lean_object* v___x_5130_; 
v___x_5128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5128_, 0, v_result_5125_);
lean_ctor_set(v___x_5128_, 1, v___y_5126_);
v___x_5129_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5129_, 0, v___x_5128_);
lean_ctor_set(v___x_5129_, 1, v___y_5127_);
v___x_5130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5130_, 0, v___x_5129_);
return v___x_5130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0___boxed(lean_object* v_lctx_5452_, lean_object* v_params_5453_, lean_object* v_As_5454_, lean_object* v_e_5455_, lean_object* v_a_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
lean_object* v_res_5459_; 
v_res_5459_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5452_, v_params_5453_, v_As_5454_, v_e_5455_, v_a_5456_, v___y_5457_, v___y_5458_);
lean_dec_ref(v___y_5457_);
lean_dec_ref(v_As_5454_);
lean_dec_ref(v_params_5453_);
return v_res_5459_;
}
}
static lean_object* _init_l_Lean4Lean_ElimNestedInductive_replaceAllNested___closed__0(void){
_start:
{
lean_object* v___x_5460_; lean_object* v___x_5461_; 
v___x_5460_ = lean_unsigned_to_nat(64u);
v___x_5461_ = l_Lean_mkPtrMap___redArg(v___x_5460_);
return v___x_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceAllNested(lean_object* v_lctx_5462_, lean_object* v_params_5463_, lean_object* v_As_5464_, lean_object* v_e_5465_, lean_object* v_a_5466_, lean_object* v_a_5467_){
_start:
{
lean_object* v___x_5468_; lean_object* v___x_5469_; 
v___x_5468_ = lean_obj_once(&l_Lean4Lean_ElimNestedInductive_replaceAllNested___closed__0, &l_Lean4Lean_ElimNestedInductive_replaceAllNested___closed__0_once, _init_l_Lean4Lean_ElimNestedInductive_replaceAllNested___closed__0);
v___x_5469_ = l_Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0(v_lctx_5462_, v_params_5463_, v_As_5464_, v_e_5465_, v___x_5468_, v_a_5466_, v_a_5467_);
if (lean_obj_tag(v___x_5469_) == 0)
{
lean_object* v_a_5470_; lean_object* v___x_5472_; uint8_t v_isShared_5473_; uint8_t v_isSharedCheck_5477_; 
v_a_5470_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5477_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5477_ == 0)
{
v___x_5472_ = v___x_5469_;
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
else
{
lean_inc(v_a_5470_);
lean_dec(v___x_5469_);
v___x_5472_ = lean_box(0);
v_isShared_5473_ = v_isSharedCheck_5477_;
goto v_resetjp_5471_;
}
v_resetjp_5471_:
{
lean_object* v___x_5475_; 
if (v_isShared_5473_ == 0)
{
v___x_5475_ = v___x_5472_;
goto v_reusejp_5474_;
}
else
{
lean_object* v_reuseFailAlloc_5476_; 
v_reuseFailAlloc_5476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_a_5470_);
v___x_5475_ = v_reuseFailAlloc_5476_;
goto v_reusejp_5474_;
}
v_reusejp_5474_:
{
return v___x_5475_;
}
}
}
else
{
lean_object* v_a_5478_; lean_object* v___x_5480_; uint8_t v_isShared_5481_; uint8_t v_isSharedCheck_5496_; 
v_a_5478_ = lean_ctor_get(v___x_5469_, 0);
v_isSharedCheck_5496_ = !lean_is_exclusive(v___x_5469_);
if (v_isSharedCheck_5496_ == 0)
{
v___x_5480_ = v___x_5469_;
v_isShared_5481_ = v_isSharedCheck_5496_;
goto v_resetjp_5479_;
}
else
{
lean_inc(v_a_5478_);
lean_dec(v___x_5469_);
v___x_5480_ = lean_box(0);
v_isShared_5481_ = v_isSharedCheck_5496_;
goto v_resetjp_5479_;
}
v_resetjp_5479_:
{
lean_object* v_fst_5482_; lean_object* v_snd_5483_; lean_object* v_fst_5484_; lean_object* v___x_5486_; uint8_t v_isShared_5487_; uint8_t v_isSharedCheck_5494_; 
v_fst_5482_ = lean_ctor_get(v_a_5478_, 0);
lean_inc(v_fst_5482_);
v_snd_5483_ = lean_ctor_get(v_a_5478_, 1);
lean_inc(v_snd_5483_);
lean_dec(v_a_5478_);
v_fst_5484_ = lean_ctor_get(v_fst_5482_, 0);
v_isSharedCheck_5494_ = !lean_is_exclusive(v_fst_5482_);
if (v_isSharedCheck_5494_ == 0)
{
lean_object* v_unused_5495_; 
v_unused_5495_ = lean_ctor_get(v_fst_5482_, 1);
lean_dec(v_unused_5495_);
v___x_5486_ = v_fst_5482_;
v_isShared_5487_ = v_isSharedCheck_5494_;
goto v_resetjp_5485_;
}
else
{
lean_inc(v_fst_5484_);
lean_dec(v_fst_5482_);
v___x_5486_ = lean_box(0);
v_isShared_5487_ = v_isSharedCheck_5494_;
goto v_resetjp_5485_;
}
v_resetjp_5485_:
{
lean_object* v___x_5489_; 
if (v_isShared_5487_ == 0)
{
lean_ctor_set(v___x_5486_, 1, v_snd_5483_);
v___x_5489_ = v___x_5486_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v_fst_5484_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_snd_5483_);
v___x_5489_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
lean_object* v___x_5491_; 
if (v_isShared_5481_ == 0)
{
lean_ctor_set(v___x_5480_, 0, v___x_5489_);
v___x_5491_ = v___x_5480_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5489_);
v___x_5491_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
return v___x_5491_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_replaceAllNested___boxed(lean_object* v_lctx_5497_, lean_object* v_params_5498_, lean_object* v_As_5499_, lean_object* v_e_5500_, lean_object* v_a_5501_, lean_object* v_a_5502_){
_start:
{
lean_object* v_res_5503_; 
v_res_5503_ = l_Lean4Lean_ElimNestedInductive_replaceAllNested(v_lctx_5497_, v_params_5498_, v_As_5499_, v_e_5500_, v_a_5501_, v_a_5502_);
lean_dec_ref(v_a_5501_);
lean_dec_ref(v_As_5499_);
lean_dec_ref(v_params_5498_);
return v_res_5503_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0(lean_object* v_00_u03b2_5504_, lean_object* v_m_5505_, lean_object* v_a_5506_){
_start:
{
lean_object* v___x_5507_; 
v___x_5507_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___redArg(v_m_5505_, v_a_5506_);
return v___x_5507_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5508_, lean_object* v_m_5509_, lean_object* v_a_5510_){
_start:
{
lean_object* v_res_5511_; 
v_res_5511_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0(v_00_u03b2_5508_, v_m_5509_, v_a_5510_);
lean_dec_ref(v_a_5510_);
lean_dec_ref(v_m_5509_);
return v_res_5511_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1(lean_object* v_00_u03b2_5512_, lean_object* v_m_5513_, lean_object* v_a_5514_, lean_object* v_b_5515_){
_start:
{
lean_object* v___x_5516_; 
v___x_5516_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1___redArg(v_m_5513_, v_a_5514_, v_b_5515_);
return v___x_5516_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5517_, lean_object* v_a_5518_, lean_object* v_x_5519_){
_start:
{
lean_object* v___x_5520_; 
v___x_5520_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___redArg(v_a_5518_, v_x_5519_);
return v___x_5520_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5521_, lean_object* v_a_5522_, lean_object* v_x_5523_){
_start:
{
lean_object* v_res_5524_; 
v_res_5524_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__0_spec__1(v_00_u03b2_5521_, v_a_5522_, v_x_5523_);
lean_dec(v_x_5523_);
lean_dec_ref(v_a_5522_);
return v_res_5524_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_5525_, lean_object* v_a_5526_, lean_object* v_x_5527_){
_start:
{
uint8_t v___x_5528_; 
v___x_5528_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___redArg(v_a_5526_, v_x_5527_);
return v___x_5528_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_5529_, lean_object* v_a_5530_, lean_object* v_x_5531_){
_start:
{
uint8_t v_res_5532_; lean_object* v_r_5533_; 
v_res_5532_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__3(v_00_u03b2_5529_, v_a_5530_, v_x_5531_);
lean_dec(v_x_5531_);
lean_dec_ref(v_a_5530_);
v_r_5533_ = lean_box(v_res_5532_);
return v_r_5533_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4(lean_object* v_00_u03b2_5534_, lean_object* v_data_5535_){
_start:
{
lean_object* v___x_5536_; 
v___x_5536_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4___redArg(v_data_5535_);
return v___x_5536_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_5537_, lean_object* v_a_5538_, lean_object* v_b_5539_, lean_object* v_x_5540_){
_start:
{
lean_object* v___x_5541_; 
v___x_5541_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__5___redArg(v_a_5538_, v_b_5539_, v_x_5540_);
return v___x_5541_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5(lean_object* v_00_u03b2_5542_, lean_object* v_i_5543_, lean_object* v_source_5544_, lean_object* v_target_5545_){
_start:
{
lean_object* v___x_5546_; 
v___x_5546_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5___redArg(v_i_5543_, v_source_5544_, v_target_5545_);
return v___x_5546_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5_spec__6(lean_object* v_00_u03b2_5547_, lean_object* v_x_5548_, lean_object* v_x_5549_){
_start:
{
lean_object* v___x_5550_; 
v___x_5550_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Expr_ReplaceImpl_replaceUnsafeT_visit___at___00Lean4Lean_ElimNestedInductive_replaceAllNested_spec__0_spec__1_spec__4_spec__5_spec__6___redArg(v_x_5548_, v_x_5549_);
return v___x_5550_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0___redArg(lean_object* v___y_5551_){
_start:
{
lean_object* v_ngen_5552_; lean_object* v_nestedAux_5553_; lean_object* v_lvls_5554_; lean_object* v_newTypes_5555_; lean_object* v_nextIdx_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5577_; 
v_ngen_5552_ = lean_ctor_get(v___y_5551_, 0);
v_nestedAux_5553_ = lean_ctor_get(v___y_5551_, 1);
v_lvls_5554_ = lean_ctor_get(v___y_5551_, 2);
v_newTypes_5555_ = lean_ctor_get(v___y_5551_, 3);
v_nextIdx_5556_ = lean_ctor_get(v___y_5551_, 4);
v_isSharedCheck_5577_ = !lean_is_exclusive(v___y_5551_);
if (v_isSharedCheck_5577_ == 0)
{
v___x_5558_ = v___y_5551_;
v_isShared_5559_ = v_isSharedCheck_5577_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_nextIdx_5556_);
lean_inc(v_newTypes_5555_);
lean_inc(v_lvls_5554_);
lean_inc(v_nestedAux_5553_);
lean_inc(v_ngen_5552_);
lean_dec(v___y_5551_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5577_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v_namePrefix_5560_; lean_object* v_idx_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5576_; 
v_namePrefix_5560_ = lean_ctor_get(v_ngen_5552_, 0);
v_idx_5561_ = lean_ctor_get(v_ngen_5552_, 1);
v_isSharedCheck_5576_ = !lean_is_exclusive(v_ngen_5552_);
if (v_isSharedCheck_5576_ == 0)
{
v___x_5563_ = v_ngen_5552_;
v_isShared_5564_ = v_isSharedCheck_5576_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_idx_5561_);
lean_inc(v_namePrefix_5560_);
lean_dec(v_ngen_5552_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5576_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v_r_5565_; lean_object* v___x_5566_; lean_object* v___x_5567_; lean_object* v___x_5569_; 
lean_inc(v_idx_5561_);
lean_inc(v_namePrefix_5560_);
v_r_5565_ = l_Lean_Name_num___override(v_namePrefix_5560_, v_idx_5561_);
v___x_5566_ = lean_unsigned_to_nat(1u);
v___x_5567_ = lean_nat_add(v_idx_5561_, v___x_5566_);
lean_dec(v_idx_5561_);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 1, v___x_5567_);
v___x_5569_ = v___x_5563_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_namePrefix_5560_);
lean_ctor_set(v_reuseFailAlloc_5575_, 1, v___x_5567_);
v___x_5569_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
lean_object* v___x_5571_; 
if (v_isShared_5559_ == 0)
{
lean_ctor_set(v___x_5558_, 0, v___x_5569_);
v___x_5571_ = v___x_5558_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v___x_5569_);
lean_ctor_set(v_reuseFailAlloc_5574_, 1, v_nestedAux_5553_);
lean_ctor_set(v_reuseFailAlloc_5574_, 2, v_lvls_5554_);
lean_ctor_set(v_reuseFailAlloc_5574_, 3, v_newTypes_5555_);
lean_ctor_set(v_reuseFailAlloc_5574_, 4, v_nextIdx_5556_);
v___x_5571_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
lean_object* v___x_5572_; lean_object* v___x_5573_; 
v___x_5572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5572_, 0, v_r_5565_);
lean_ctor_set(v___x_5572_, 1, v___x_5571_);
v___x_5573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5573_, 0, v___x_5572_);
return v___x_5573_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0(lean_object* v___y_5578_, lean_object* v___y_5579_){
_start:
{
lean_object* v___x_5580_; 
v___x_5580_ = l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0___redArg(v___y_5579_);
return v___x_5580_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0___boxed(lean_object* v___y_5581_, lean_object* v___y_5582_){
_start:
{
lean_object* v_res_5583_; 
v_res_5583_ = l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0(v___y_5581_, v___y_5582_);
lean_dec_ref(v___y_5581_);
return v_res_5583_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg(lean_object* v_k_5589_, lean_object* v_lctx_5590_, lean_object* v_type_5591_, lean_object* v_params_5592_, lean_object* v_x_5593_, lean_object* v_a_5594_, lean_object* v_a_5595_){
_start:
{
lean_object* v_zero_5596_; uint8_t v_isZero_5597_; 
v_zero_5596_ = lean_unsigned_to_nat(0u);
v_isZero_5597_ = lean_nat_dec_eq(v_x_5593_, v_zero_5596_);
if (v_isZero_5597_ == 1)
{
lean_object* v___x_5598_; 
lean_dec(v_x_5593_);
lean_inc_ref(v_a_5594_);
v___x_5598_ = lean_apply_5(v_k_5589_, v_lctx_5590_, v_type_5591_, v_params_5592_, v_a_5594_, v_a_5595_);
return v___x_5598_;
}
else
{
if (lean_obj_tag(v_type_5591_) == 7)
{
lean_object* v_binderName_5599_; lean_object* v_binderType_5600_; lean_object* v_body_5601_; uint8_t v_binderInfo_5602_; lean_object* v___x_5603_; lean_object* v_a_5604_; lean_object* v_fst_5605_; lean_object* v_snd_5606_; lean_object* v_one_5607_; lean_object* v_n_5608_; uint8_t v___x_5609_; lean_object* v___x_5610_; lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___x_5613_; 
v_binderName_5599_ = lean_ctor_get(v_type_5591_, 0);
lean_inc(v_binderName_5599_);
v_binderType_5600_ = lean_ctor_get(v_type_5591_, 1);
lean_inc_ref(v_binderType_5600_);
v_body_5601_ = lean_ctor_get(v_type_5591_, 2);
lean_inc_ref(v_body_5601_);
v_binderInfo_5602_ = lean_ctor_get_uint8(v_type_5591_, sizeof(void*)*3 + 8);
lean_dec_ref(v_type_5591_);
v___x_5603_ = l_Lean_mkFreshId___at___00Lean4Lean_ElimNestedInductive_withParams_loop_spec__0___redArg(v_a_5595_);
v_a_5604_ = lean_ctor_get(v___x_5603_, 0);
lean_inc(v_a_5604_);
lean_dec_ref(v___x_5603_);
v_fst_5605_ = lean_ctor_get(v_a_5604_, 0);
lean_inc_n(v_fst_5605_, 2);
v_snd_5606_ = lean_ctor_get(v_a_5604_, 1);
lean_inc(v_snd_5606_);
lean_dec(v_a_5604_);
v_one_5607_ = lean_unsigned_to_nat(1u);
v_n_5608_ = lean_nat_sub(v_x_5593_, v_one_5607_);
lean_dec(v_x_5593_);
v___x_5609_ = 0;
v___x_5610_ = l_Lean_LocalContext_mkLocalDecl(v_lctx_5590_, v_fst_5605_, v_binderName_5599_, v_binderType_5600_, v_binderInfo_5602_, v___x_5609_);
v___x_5611_ = l_Lean_Expr_fvar___override(v_fst_5605_);
v___x_5612_ = lean_expr_instantiate1(v_body_5601_, v___x_5611_);
lean_dec_ref(v_body_5601_);
v___x_5613_ = lean_array_push(v_params_5592_, v___x_5611_);
v_lctx_5590_ = v___x_5610_;
v_type_5591_ = v___x_5612_;
v_params_5592_ = v___x_5613_;
v_x_5593_ = v_n_5608_;
v_a_5595_ = v_snd_5606_;
goto _start;
}
else
{
lean_object* v___x_5615_; 
lean_dec_ref(v_a_5595_);
lean_dec(v_x_5593_);
lean_dec_ref(v_params_5592_);
lean_dec_ref(v_type_5591_);
lean_dec_ref(v_lctx_5590_);
lean_dec_ref(v_k_5589_);
v___x_5615_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___closed__2));
return v___x_5615_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg___boxed(lean_object* v_k_5616_, lean_object* v_lctx_5617_, lean_object* v_type_5618_, lean_object* v_params_5619_, lean_object* v_x_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_){
_start:
{
lean_object* v_res_5623_; 
v_res_5623_ = l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg(v_k_5616_, v_lctx_5617_, v_type_5618_, v_params_5619_, v_x_5620_, v_a_5621_, v_a_5622_);
lean_dec_ref(v_a_5621_);
return v_res_5623_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop(lean_object* v_00_u03b1_5624_, lean_object* v_k_5625_, lean_object* v_lctx_5626_, lean_object* v_type_5627_, lean_object* v_params_5628_, lean_object* v_x_5629_, lean_object* v_a_5630_, lean_object* v_a_5631_){
_start:
{
lean_object* v___x_5632_; 
v___x_5632_ = l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg(v_k_5625_, v_lctx_5626_, v_type_5627_, v_params_5628_, v_x_5629_, v_a_5630_, v_a_5631_);
return v___x_5632_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams_loop___boxed(lean_object* v_00_u03b1_5633_, lean_object* v_k_5634_, lean_object* v_lctx_5635_, lean_object* v_type_5636_, lean_object* v_params_5637_, lean_object* v_x_5638_, lean_object* v_a_5639_, lean_object* v_a_5640_){
_start:
{
lean_object* v_res_5641_; 
v_res_5641_ = l_Lean4Lean_ElimNestedInductive_withParams_loop(v_00_u03b1_5633_, v_k_5634_, v_lctx_5635_, v_type_5636_, v_params_5637_, v_x_5638_, v_a_5639_, v_a_5640_);
lean_dec_ref(v_a_5639_);
return v_res_5641_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams___redArg(lean_object* v_type_5642_, lean_object* v_nparams_5643_, lean_object* v_k_5644_, lean_object* v_a_5645_, lean_object* v_a_5646_){
_start:
{
lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5649_; lean_object* v___x_5650_; lean_object* v___x_5651_; 
v___x_5647_ = lean_unsigned_to_nat(32u);
v___x_5648_ = lean_mk_empty_array_with_capacity(v___x_5647_);
lean_dec_ref(v___x_5648_);
v___x_5649_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4);
v___x_5650_ = ((lean_object*)(l_Lean4Lean_AddInductive_isLargeEliminator___closed__0));
v___x_5651_ = l_Lean4Lean_ElimNestedInductive_withParams_loop___redArg(v_k_5644_, v___x_5649_, v_type_5642_, v___x_5650_, v_nparams_5643_, v_a_5645_, v_a_5646_);
return v___x_5651_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams___redArg___boxed(lean_object* v_type_5652_, lean_object* v_nparams_5653_, lean_object* v_k_5654_, lean_object* v_a_5655_, lean_object* v_a_5656_){
_start:
{
lean_object* v_res_5657_; 
v_res_5657_ = l_Lean4Lean_ElimNestedInductive_withParams___redArg(v_type_5652_, v_nparams_5653_, v_k_5654_, v_a_5655_, v_a_5656_);
lean_dec_ref(v_a_5655_);
return v_res_5657_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams(lean_object* v_00_u03b1_5658_, lean_object* v_type_5659_, lean_object* v_nparams_5660_, lean_object* v_k_5661_, lean_object* v_a_5662_, lean_object* v_a_5663_){
_start:
{
lean_object* v___x_5664_; 
v___x_5664_ = l_Lean4Lean_ElimNestedInductive_withParams___redArg(v_type_5659_, v_nparams_5660_, v_k_5661_, v_a_5662_, v_a_5663_);
return v___x_5664_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_withParams___boxed(lean_object* v_00_u03b1_5665_, lean_object* v_type_5666_, lean_object* v_nparams_5667_, lean_object* v_k_5668_, lean_object* v_a_5669_, lean_object* v_a_5670_){
_start:
{
lean_object* v_res_5671_; 
v_res_5671_ = l_Lean4Lean_ElimNestedInductive_withParams(v_00_u03b1_5665_, v_type_5666_, v_nparams_5667_, v_k_5668_, v_a_5669_, v_a_5670_);
lean_dec_ref(v_a_5669_);
return v_res_5671_;
}
}
static lean_object* _init_l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___closed__0(void){
_start:
{
lean_object* v___x_5672_; lean_object* v___x_5673_; lean_object* v___x_5674_; 
v___x_5672_ = l_Lean_instInhabitedConstructor_default;
v___x_5673_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12));
v___x_5674_ = l_instInhabitedOfMonad___redArg(v___x_5673_, v___x_5672_);
return v___x_5674_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0(lean_object* v_msg_5675_, lean_object* v___y_5676_, lean_object* v___y_5677_){
_start:
{
lean_object* v___x_5678_; lean_object* v___f_5679_; lean_object* v___x_2855__overap_5680_; lean_object* v___x_5681_; 
v___x_5678_ = lean_obj_once(&l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___closed__0, &l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___closed__0_once, _init_l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___closed__0);
v___f_5679_ = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_5679_, 0, v___x_5678_);
v___x_2855__overap_5680_ = lean_panic_fn_borrowed(v___f_5679_, v_msg_5675_);
lean_dec_ref(v___f_5679_);
lean_inc_ref(v___y_5676_);
v___x_5681_ = lean_apply_2(v___x_2855__overap_5680_, v___y_5676_, v___y_5677_);
return v___x_5681_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0___boxed(lean_object* v_msg_5682_, lean_object* v___y_5683_, lean_object* v___y_5684_){
_start:
{
lean_object* v_res_5685_; 
v_res_5685_ = l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0(v_msg_5682_, v___y_5683_, v___y_5684_);
lean_dec_ref(v___y_5683_);
return v_res_5685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__1(lean_object* v_params_5686_, lean_object* v_as_5687_, size_t v_i_5688_, size_t v_stop_5689_, lean_object* v_b_5690_){
_start:
{
uint8_t v___x_5691_; 
v___x_5691_ = lean_usize_dec_eq(v_i_5688_, v_stop_5689_);
if (v___x_5691_ == 0)
{
lean_object* v___x_5692_; lean_object* v_fst_5693_; lean_object* v_snd_5694_; lean_object* v___x_5695_; lean_object* v___x_5696_; size_t v___x_5697_; size_t v___x_5698_; 
v___x_5692_ = lean_array_uget_borrowed(v_as_5687_, v_i_5688_);
v_fst_5693_ = lean_ctor_get(v___x_5692_, 0);
v_snd_5694_ = lean_ctor_get(v___x_5692_, 1);
v___x_5695_ = lean_expr_abstract(v_fst_5693_, v_params_5686_);
lean_inc(v_snd_5694_);
v___x_5696_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_snd_5694_, v___x_5695_, v_b_5690_);
v___x_5697_ = ((size_t)1ULL);
v___x_5698_ = lean_usize_add(v_i_5688_, v___x_5697_);
v_i_5688_ = v___x_5698_;
v_b_5690_ = v___x_5696_;
goto _start;
}
else
{
return v_b_5690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__1___boxed(lean_object* v_params_5700_, lean_object* v_as_5701_, lean_object* v_i_5702_, lean_object* v_stop_5703_, lean_object* v_b_5704_){
_start:
{
size_t v_i_boxed_5705_; size_t v_stop_boxed_5706_; lean_object* v_res_5707_; 
v_i_boxed_5705_ = lean_unbox_usize(v_i_5702_);
lean_dec(v_i_5702_);
v_stop_boxed_5706_ = lean_unbox_usize(v_stop_5703_);
lean_dec(v_stop_5703_);
v_res_5707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__1(v_params_5700_, v_as_5701_, v_i_boxed_5705_, v_stop_boxed_5706_, v_b_5704_);
lean_dec_ref(v_as_5701_);
lean_dec_ref(v_params_5700_);
return v_res_5707_;
}
}
static lean_object* _init_l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__2(void){
_start:
{
lean_object* v___x_5710_; lean_object* v___x_5711_; lean_object* v___x_5712_; lean_object* v___x_5713_; lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5710_ = ((lean_object*)(l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__1));
v___x_5711_ = lean_unsigned_to_nat(8u);
v___x_5712_ = lean_unsigned_to_nat(693u);
v___x_5713_ = ((lean_object*)(l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__0));
v___x_5714_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_5715_ = l_mkPanicMessageWithDecl(v___x_5714_, v___x_5713_, v___x_5712_, v___x_5711_, v___x_5710_);
return v___x_5715_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0(lean_object* v_nparams_5716_, lean_object* v_params_5717_, lean_object* v_name_5718_, lean_object* v_lctx_5719_, lean_object* v_ctorType_5720_, lean_object* v_As_5721_, lean_object* v___y_5722_, lean_object* v___y_5723_){
_start:
{
lean_object* v___x_5724_; uint8_t v___x_5725_; 
v___x_5724_ = lean_array_get_size(v_As_5721_);
v___x_5725_ = lean_nat_dec_eq(v___x_5724_, v_nparams_5716_);
if (v___x_5725_ == 0)
{
lean_object* v___x_5726_; lean_object* v___x_5727_; 
lean_dec_ref(v_ctorType_5720_);
lean_dec_ref(v_lctx_5719_);
lean_dec(v_name_5718_);
v___x_5726_ = lean_obj_once(&l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__2, &l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__2_once, _init_l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___closed__2);
v___x_5727_ = l_panic___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__0(v___x_5726_, v___y_5722_, v___y_5723_);
return v___x_5727_;
}
else
{
lean_object* v___x_5728_; 
lean_inc_ref(v_lctx_5719_);
v___x_5728_ = l_Lean4Lean_ElimNestedInductive_replaceAllNested(v_lctx_5719_, v_params_5717_, v_As_5721_, v_ctorType_5720_, v___y_5722_, v___y_5723_);
if (lean_obj_tag(v___x_5728_) == 0)
{
lean_object* v_a_5729_; lean_object* v___x_5731_; uint8_t v_isShared_5732_; uint8_t v_isSharedCheck_5736_; 
lean_dec_ref(v_lctx_5719_);
lean_dec(v_name_5718_);
v_a_5729_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5736_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5736_ == 0)
{
v___x_5731_ = v___x_5728_;
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
else
{
lean_inc(v_a_5729_);
lean_dec(v___x_5728_);
v___x_5731_ = lean_box(0);
v_isShared_5732_ = v_isSharedCheck_5736_;
goto v_resetjp_5730_;
}
v_resetjp_5730_:
{
lean_object* v___x_5734_; 
if (v_isShared_5732_ == 0)
{
v___x_5734_ = v___x_5731_;
goto v_reusejp_5733_;
}
else
{
lean_object* v_reuseFailAlloc_5735_; 
v_reuseFailAlloc_5735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5735_, 0, v_a_5729_);
v___x_5734_ = v_reuseFailAlloc_5735_;
goto v_reusejp_5733_;
}
v_reusejp_5733_:
{
return v___x_5734_;
}
}
}
else
{
lean_object* v_a_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5756_; 
v_a_5737_ = lean_ctor_get(v___x_5728_, 0);
v_isSharedCheck_5756_ = !lean_is_exclusive(v___x_5728_);
if (v_isSharedCheck_5756_ == 0)
{
v___x_5739_ = v___x_5728_;
v_isShared_5740_ = v_isSharedCheck_5756_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_a_5737_);
lean_dec(v___x_5728_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5756_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v_fst_5741_; lean_object* v_snd_5742_; lean_object* v___x_5744_; uint8_t v_isShared_5745_; uint8_t v_isSharedCheck_5755_; 
v_fst_5741_ = lean_ctor_get(v_a_5737_, 0);
v_snd_5742_ = lean_ctor_get(v_a_5737_, 1);
v_isSharedCheck_5755_ = !lean_is_exclusive(v_a_5737_);
if (v_isSharedCheck_5755_ == 0)
{
v___x_5744_ = v_a_5737_;
v_isShared_5745_ = v_isSharedCheck_5755_;
goto v_resetjp_5743_;
}
else
{
lean_inc(v_snd_5742_);
lean_inc(v_fst_5741_);
lean_dec(v_a_5737_);
v___x_5744_ = lean_box(0);
v_isShared_5745_ = v_isSharedCheck_5755_;
goto v_resetjp_5743_;
}
v_resetjp_5743_:
{
uint8_t v___x_5746_; lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5750_; 
v___x_5746_ = 0;
v___x_5747_ = l_Lean_LocalContext_mkForall(v_lctx_5719_, v_As_5721_, v_fst_5741_, v___x_5725_, v___x_5746_);
lean_dec(v_fst_5741_);
v___x_5748_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5748_, 0, v_name_5718_);
lean_ctor_set(v___x_5748_, 1, v___x_5747_);
if (v_isShared_5745_ == 0)
{
lean_ctor_set(v___x_5744_, 0, v___x_5748_);
v___x_5750_ = v___x_5744_;
goto v_reusejp_5749_;
}
else
{
lean_object* v_reuseFailAlloc_5754_; 
v_reuseFailAlloc_5754_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5754_, 0, v___x_5748_);
lean_ctor_set(v_reuseFailAlloc_5754_, 1, v_snd_5742_);
v___x_5750_ = v_reuseFailAlloc_5754_;
goto v_reusejp_5749_;
}
v_reusejp_5749_:
{
lean_object* v___x_5752_; 
if (v_isShared_5740_ == 0)
{
lean_ctor_set(v___x_5739_, 0, v___x_5750_);
v___x_5752_ = v___x_5739_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v___x_5750_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___boxed(lean_object* v_nparams_5757_, lean_object* v_params_5758_, lean_object* v_name_5759_, lean_object* v_lctx_5760_, lean_object* v_ctorType_5761_, lean_object* v_As_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0(v_nparams_5757_, v_params_5758_, v_name_5759_, v_lctx_5760_, v_ctorType_5761_, v_As_5762_, v___y_5763_, v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec_ref(v_As_5762_);
lean_dec_ref(v_params_5758_);
lean_dec(v_nparams_5757_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2(lean_object* v_nparams_5766_, lean_object* v_params_5767_, lean_object* v_x_5768_, lean_object* v_x_5769_, lean_object* v___y_5770_, lean_object* v___y_5771_){
_start:
{
if (lean_obj_tag(v_x_5768_) == 0)
{
lean_object* v___x_5772_; lean_object* v___x_5773_; lean_object* v___x_5774_; 
lean_dec_ref(v_params_5767_);
lean_dec(v_nparams_5766_);
v___x_5772_ = l_List_reverse___redArg(v_x_5769_);
v___x_5773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5773_, 0, v___x_5772_);
lean_ctor_set(v___x_5773_, 1, v___y_5771_);
v___x_5774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5774_, 0, v___x_5773_);
return v___x_5774_;
}
else
{
lean_object* v_head_5775_; lean_object* v_tail_5776_; lean_object* v___x_5778_; uint8_t v_isShared_5779_; uint8_t v_isSharedCheck_5799_; 
v_head_5775_ = lean_ctor_get(v_x_5768_, 0);
v_tail_5776_ = lean_ctor_get(v_x_5768_, 1);
v_isSharedCheck_5799_ = !lean_is_exclusive(v_x_5768_);
if (v_isSharedCheck_5799_ == 0)
{
v___x_5778_ = v_x_5768_;
v_isShared_5779_ = v_isSharedCheck_5799_;
goto v_resetjp_5777_;
}
else
{
lean_inc(v_tail_5776_);
lean_inc(v_head_5775_);
lean_dec(v_x_5768_);
v___x_5778_ = lean_box(0);
v_isShared_5779_ = v_isSharedCheck_5799_;
goto v_resetjp_5777_;
}
v_resetjp_5777_:
{
lean_object* v_name_5780_; lean_object* v_type_5781_; lean_object* v___f_5782_; lean_object* v___x_5783_; 
v_name_5780_ = lean_ctor_get(v_head_5775_, 0);
lean_inc(v_name_5780_);
v_type_5781_ = lean_ctor_get(v_head_5775_, 1);
lean_inc_ref(v_type_5781_);
lean_dec(v_head_5775_);
lean_inc_ref(v_params_5767_);
lean_inc_n(v_nparams_5766_, 2);
v___f_5782_ = lean_alloc_closure((void*)(l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___lam__0___boxed), 8, 3);
lean_closure_set(v___f_5782_, 0, v_nparams_5766_);
lean_closure_set(v___f_5782_, 1, v_params_5767_);
lean_closure_set(v___f_5782_, 2, v_name_5780_);
v___x_5783_ = l_Lean4Lean_ElimNestedInductive_withParams___redArg(v_type_5781_, v_nparams_5766_, v___f_5782_, v___y_5770_, v___y_5771_);
if (lean_obj_tag(v___x_5783_) == 0)
{
lean_object* v_a_5784_; lean_object* v___x_5786_; uint8_t v_isShared_5787_; uint8_t v_isSharedCheck_5791_; 
lean_del_object(v___x_5778_);
lean_dec(v_tail_5776_);
lean_dec(v_x_5769_);
lean_dec_ref(v_params_5767_);
lean_dec(v_nparams_5766_);
v_a_5784_ = lean_ctor_get(v___x_5783_, 0);
v_isSharedCheck_5791_ = !lean_is_exclusive(v___x_5783_);
if (v_isSharedCheck_5791_ == 0)
{
v___x_5786_ = v___x_5783_;
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
else
{
lean_inc(v_a_5784_);
lean_dec(v___x_5783_);
v___x_5786_ = lean_box(0);
v_isShared_5787_ = v_isSharedCheck_5791_;
goto v_resetjp_5785_;
}
v_resetjp_5785_:
{
lean_object* v___x_5789_; 
if (v_isShared_5787_ == 0)
{
v___x_5789_ = v___x_5786_;
goto v_reusejp_5788_;
}
else
{
lean_object* v_reuseFailAlloc_5790_; 
v_reuseFailAlloc_5790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
v___x_5789_ = v_reuseFailAlloc_5790_;
goto v_reusejp_5788_;
}
v_reusejp_5788_:
{
return v___x_5789_;
}
}
}
else
{
lean_object* v_a_5792_; lean_object* v_fst_5793_; lean_object* v_snd_5794_; lean_object* v___x_5796_; 
v_a_5792_ = lean_ctor_get(v___x_5783_, 0);
lean_inc(v_a_5792_);
lean_dec_ref(v___x_5783_);
v_fst_5793_ = lean_ctor_get(v_a_5792_, 0);
lean_inc(v_fst_5793_);
v_snd_5794_ = lean_ctor_get(v_a_5792_, 1);
lean_inc(v_snd_5794_);
lean_dec(v_a_5792_);
if (v_isShared_5779_ == 0)
{
lean_ctor_set(v___x_5778_, 1, v_x_5769_);
lean_ctor_set(v___x_5778_, 0, v_fst_5793_);
v___x_5796_ = v___x_5778_;
goto v_reusejp_5795_;
}
else
{
lean_object* v_reuseFailAlloc_5798_; 
v_reuseFailAlloc_5798_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_fst_5793_);
lean_ctor_set(v_reuseFailAlloc_5798_, 1, v_x_5769_);
v___x_5796_ = v_reuseFailAlloc_5798_;
goto v_reusejp_5795_;
}
v_reusejp_5795_:
{
v_x_5768_ = v_tail_5776_;
v_x_5769_ = v___x_5796_;
v___y_5771_ = v_snd_5794_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2___boxed(lean_object* v_nparams_5800_, lean_object* v_params_5801_, lean_object* v_x_5802_, lean_object* v_x_5803_, lean_object* v___y_5804_, lean_object* v___y_5805_){
_start:
{
lean_object* v_res_5806_; 
v_res_5806_ = l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2(v_nparams_5800_, v_params_5801_, v_x_5802_, v_x_5803_, v___y_5804_, v___y_5805_);
lean_dec_ref(v___y_5804_);
return v_res_5806_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run_loop(lean_object* v_nparams_5812_, lean_object* v_params_5813_, lean_object* v_i_5814_, lean_object* v_x_5815_, lean_object* v_a_5816_, lean_object* v_a_5817_){
_start:
{
lean_object* v_zero_5818_; uint8_t v_isZero_5819_; 
v_zero_5818_ = lean_unsigned_to_nat(0u);
v_isZero_5819_ = lean_nat_dec_eq(v_x_5815_, v_zero_5818_);
if (v_isZero_5819_ == 1)
{
lean_object* v___x_5820_; 
lean_dec_ref(v_a_5817_);
lean_dec(v_x_5815_);
lean_dec(v_i_5814_);
lean_dec_ref(v_params_5813_);
lean_dec(v_nparams_5812_);
v___x_5820_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_run_loop___closed__2));
return v___x_5820_;
}
else
{
lean_object* v_ngen_5821_; lean_object* v_nestedAux_5822_; lean_object* v_newTypes_5823_; lean_object* v___y_5825_; lean_object* v___x_5831_; uint8_t v___x_5832_; 
v_ngen_5821_ = lean_ctor_get(v_a_5817_, 0);
v_nestedAux_5822_ = lean_ctor_get(v_a_5817_, 1);
v_newTypes_5823_ = lean_ctor_get(v_a_5817_, 3);
v___x_5831_ = lean_array_get_size(v_newTypes_5823_);
v___x_5832_ = lean_nat_dec_lt(v_i_5814_, v___x_5831_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5833_; lean_object* v___x_5834_; uint8_t v___x_5835_; 
lean_dec(v_x_5815_);
lean_dec(v_i_5814_);
lean_dec(v_nparams_5812_);
v___x_5833_ = lean_box(1);
v___x_5834_ = lean_array_get_size(v_nestedAux_5822_);
v___x_5835_ = lean_nat_dec_lt(v_zero_5818_, v___x_5834_);
if (v___x_5835_ == 0)
{
v___y_5825_ = v___x_5833_;
goto v___jp_5824_;
}
else
{
uint8_t v___x_5836_; 
v___x_5836_ = lean_nat_dec_le(v___x_5834_, v___x_5834_);
if (v___x_5836_ == 0)
{
if (v___x_5835_ == 0)
{
v___y_5825_ = v___x_5833_;
goto v___jp_5824_;
}
else
{
size_t v___x_5837_; size_t v___x_5838_; lean_object* v___x_5839_; 
v___x_5837_ = ((size_t)0ULL);
v___x_5838_ = lean_usize_of_nat(v___x_5834_);
v___x_5839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__1(v_params_5813_, v_nestedAux_5822_, v___x_5837_, v___x_5838_, v___x_5833_);
v___y_5825_ = v___x_5839_;
goto v___jp_5824_;
}
}
else
{
size_t v___x_5840_; size_t v___x_5841_; lean_object* v___x_5842_; 
v___x_5840_ = ((size_t)0ULL);
v___x_5841_ = lean_usize_of_nat(v___x_5834_);
v___x_5842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__1(v_params_5813_, v_nestedAux_5822_, v___x_5840_, v___x_5841_, v___x_5833_);
v___y_5825_ = v___x_5842_;
goto v___jp_5824_;
}
}
}
else
{
lean_object* v___x_5843_; lean_object* v_name_5844_; lean_object* v_type_5845_; lean_object* v_ctors_5846_; lean_object* v___x_5848_; uint8_t v_isShared_5849_; uint8_t v_isSharedCheck_5883_; 
v___x_5843_ = lean_array_fget(v_newTypes_5823_, v_i_5814_);
v_name_5844_ = lean_ctor_get(v___x_5843_, 0);
v_type_5845_ = lean_ctor_get(v___x_5843_, 1);
v_ctors_5846_ = lean_ctor_get(v___x_5843_, 2);
v_isSharedCheck_5883_ = !lean_is_exclusive(v___x_5843_);
if (v_isSharedCheck_5883_ == 0)
{
v___x_5848_ = v___x_5843_;
v_isShared_5849_ = v_isSharedCheck_5883_;
goto v_resetjp_5847_;
}
else
{
lean_inc(v_ctors_5846_);
lean_inc(v_type_5845_);
lean_inc(v_name_5844_);
lean_dec(v___x_5843_);
v___x_5848_ = lean_box(0);
v_isShared_5849_ = v_isSharedCheck_5883_;
goto v_resetjp_5847_;
}
v_resetjp_5847_:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5850_ = lean_box(0);
lean_inc_ref(v_params_5813_);
lean_inc(v_nparams_5812_);
v___x_5851_ = l_List_mapM_loop___at___00Lean4Lean_ElimNestedInductive_run_loop_spec__2(v_nparams_5812_, v_params_5813_, v_ctors_5846_, v___x_5850_, v_a_5816_, v_a_5817_);
if (lean_obj_tag(v___x_5851_) == 0)
{
lean_object* v_a_5852_; lean_object* v___x_5854_; uint8_t v_isShared_5855_; uint8_t v_isSharedCheck_5859_; 
lean_del_object(v___x_5848_);
lean_dec_ref(v_type_5845_);
lean_dec(v_name_5844_);
lean_dec(v_x_5815_);
lean_dec(v_i_5814_);
lean_dec_ref(v_params_5813_);
lean_dec(v_nparams_5812_);
v_a_5852_ = lean_ctor_get(v___x_5851_, 0);
v_isSharedCheck_5859_ = !lean_is_exclusive(v___x_5851_);
if (v_isSharedCheck_5859_ == 0)
{
v___x_5854_ = v___x_5851_;
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
else
{
lean_inc(v_a_5852_);
lean_dec(v___x_5851_);
v___x_5854_ = lean_box(0);
v_isShared_5855_ = v_isSharedCheck_5859_;
goto v_resetjp_5853_;
}
v_resetjp_5853_:
{
lean_object* v___x_5857_; 
if (v_isShared_5855_ == 0)
{
v___x_5857_ = v___x_5854_;
goto v_reusejp_5856_;
}
else
{
lean_object* v_reuseFailAlloc_5858_; 
v_reuseFailAlloc_5858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5858_, 0, v_a_5852_);
v___x_5857_ = v_reuseFailAlloc_5858_;
goto v_reusejp_5856_;
}
v_reusejp_5856_:
{
return v___x_5857_;
}
}
}
else
{
lean_object* v_a_5860_; lean_object* v_snd_5861_; lean_object* v_fst_5862_; lean_object* v_ngen_5863_; lean_object* v_nestedAux_5864_; lean_object* v_lvls_5865_; lean_object* v_newTypes_5866_; lean_object* v_nextIdx_5867_; lean_object* v___x_5869_; uint8_t v_isShared_5870_; uint8_t v_isSharedCheck_5882_; 
v_a_5860_ = lean_ctor_get(v___x_5851_, 0);
lean_inc(v_a_5860_);
lean_dec_ref(v___x_5851_);
v_snd_5861_ = lean_ctor_get(v_a_5860_, 1);
lean_inc(v_snd_5861_);
v_fst_5862_ = lean_ctor_get(v_a_5860_, 0);
lean_inc(v_fst_5862_);
lean_dec(v_a_5860_);
v_ngen_5863_ = lean_ctor_get(v_snd_5861_, 0);
v_nestedAux_5864_ = lean_ctor_get(v_snd_5861_, 1);
v_lvls_5865_ = lean_ctor_get(v_snd_5861_, 2);
v_newTypes_5866_ = lean_ctor_get(v_snd_5861_, 3);
v_nextIdx_5867_ = lean_ctor_get(v_snd_5861_, 4);
v_isSharedCheck_5882_ = !lean_is_exclusive(v_snd_5861_);
if (v_isSharedCheck_5882_ == 0)
{
v___x_5869_ = v_snd_5861_;
v_isShared_5870_ = v_isSharedCheck_5882_;
goto v_resetjp_5868_;
}
else
{
lean_inc(v_nextIdx_5867_);
lean_inc(v_newTypes_5866_);
lean_inc(v_lvls_5865_);
lean_inc(v_nestedAux_5864_);
lean_inc(v_ngen_5863_);
lean_dec(v_snd_5861_);
v___x_5869_ = lean_box(0);
v_isShared_5870_ = v_isSharedCheck_5882_;
goto v_resetjp_5868_;
}
v_resetjp_5868_:
{
lean_object* v_one_5871_; lean_object* v_n_5872_; lean_object* v___x_5874_; 
v_one_5871_ = lean_unsigned_to_nat(1u);
v_n_5872_ = lean_nat_sub(v_x_5815_, v_one_5871_);
lean_dec(v_x_5815_);
if (v_isShared_5849_ == 0)
{
lean_ctor_set(v___x_5848_, 2, v_fst_5862_);
v___x_5874_ = v___x_5848_;
goto v_reusejp_5873_;
}
else
{
lean_object* v_reuseFailAlloc_5881_; 
v_reuseFailAlloc_5881_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_5881_, 0, v_name_5844_);
lean_ctor_set(v_reuseFailAlloc_5881_, 1, v_type_5845_);
lean_ctor_set(v_reuseFailAlloc_5881_, 2, v_fst_5862_);
v___x_5874_ = v_reuseFailAlloc_5881_;
goto v_reusejp_5873_;
}
v_reusejp_5873_:
{
lean_object* v___x_5875_; lean_object* v___x_5877_; 
v___x_5875_ = lean_array_set(v_newTypes_5866_, v_i_5814_, v___x_5874_);
if (v_isShared_5870_ == 0)
{
lean_ctor_set(v___x_5869_, 3, v___x_5875_);
v___x_5877_ = v___x_5869_;
goto v_reusejp_5876_;
}
else
{
lean_object* v_reuseFailAlloc_5880_; 
v_reuseFailAlloc_5880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5880_, 0, v_ngen_5863_);
lean_ctor_set(v_reuseFailAlloc_5880_, 1, v_nestedAux_5864_);
lean_ctor_set(v_reuseFailAlloc_5880_, 2, v_lvls_5865_);
lean_ctor_set(v_reuseFailAlloc_5880_, 3, v___x_5875_);
lean_ctor_set(v_reuseFailAlloc_5880_, 4, v_nextIdx_5867_);
v___x_5877_ = v_reuseFailAlloc_5880_;
goto v_reusejp_5876_;
}
v_reusejp_5876_:
{
lean_object* v___x_5878_; 
v___x_5878_ = lean_nat_add(v_i_5814_, v_one_5871_);
lean_dec(v_i_5814_);
v_i_5814_ = v___x_5878_;
v_x_5815_ = v_n_5872_;
v_a_5817_ = v___x_5877_;
goto _start;
}
}
}
}
}
}
v___jp_5824_:
{
lean_object* v___x_5826_; lean_object* v___x_5827_; lean_object* v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5826_ = lean_array_get_size(v_params_5813_);
lean_dec_ref(v_params_5813_);
lean_inc_ref(v_newTypes_5823_);
v___x_5827_ = lean_array_to_list(v_newTypes_5823_);
lean_inc_ref(v_ngen_5821_);
v___x_5828_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5828_, 0, v_ngen_5821_);
lean_ctor_set(v___x_5828_, 1, v___x_5826_);
lean_ctor_set(v___x_5828_, 2, v___y_5825_);
lean_ctor_set(v___x_5828_, 3, v___x_5827_);
v___x_5829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5829_, 0, v___x_5828_);
lean_ctor_set(v___x_5829_, 1, v_a_5817_);
v___x_5830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5829_);
return v___x_5830_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run_loop___boxed(lean_object* v_nparams_5884_, lean_object* v_params_5885_, lean_object* v_i_5886_, lean_object* v_x_5887_, lean_object* v_a_5888_, lean_object* v_a_5889_){
_start:
{
lean_object* v_res_5890_; 
v_res_5890_ = l_Lean4Lean_ElimNestedInductive_run_loop(v_nparams_5884_, v_params_5885_, v_i_5886_, v_x_5887_, v_a_5888_, v_a_5889_);
lean_dec_ref(v_a_5888_);
return v_res_5890_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run___lam__0(lean_object* v_nparams_5891_, lean_object* v_x_5892_, lean_object* v_x_5893_, lean_object* v_params_5894_, lean_object* v___y_5895_, lean_object* v___y_5896_){
_start:
{
lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; 
v___x_5897_ = lean_unsigned_to_nat(0u);
v___x_5898_ = lean_unsigned_to_nat(1000u);
v___x_5899_ = l_Lean4Lean_ElimNestedInductive_run_loop(v_nparams_5891_, v_params_5894_, v___x_5897_, v___x_5898_, v___y_5895_, v___y_5896_);
return v___x_5899_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run___lam__0___boxed(lean_object* v_nparams_5900_, lean_object* v_x_5901_, lean_object* v_x_5902_, lean_object* v_params_5903_, lean_object* v___y_5904_, lean_object* v___y_5905_){
_start:
{
lean_object* v_res_5906_; 
v_res_5906_ = l_Lean4Lean_ElimNestedInductive_run___lam__0(v_nparams_5900_, v_x_5901_, v_x_5902_, v_params_5903_, v___y_5904_, v___y_5905_);
lean_dec_ref(v___y_5904_);
lean_dec_ref(v_x_5902_);
lean_dec_ref(v_x_5901_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run(lean_object* v_nparams_5912_, lean_object* v_types_5913_, lean_object* v_a_5914_, lean_object* v_a_5915_){
_start:
{
if (lean_obj_tag(v_types_5913_) == 1)
{
lean_object* v_head_5916_; lean_object* v_type_5917_; lean_object* v___f_5918_; lean_object* v___x_5919_; 
v_head_5916_ = lean_ctor_get(v_types_5913_, 0);
lean_inc(v_head_5916_);
lean_dec_ref(v_types_5913_);
v_type_5917_ = lean_ctor_get(v_head_5916_, 1);
lean_inc_ref(v_type_5917_);
lean_dec(v_head_5916_);
lean_inc(v_nparams_5912_);
v___f_5918_ = lean_alloc_closure((void*)(l_Lean4Lean_ElimNestedInductive_run___lam__0___boxed), 6, 1);
lean_closure_set(v___f_5918_, 0, v_nparams_5912_);
v___x_5919_ = l_Lean4Lean_ElimNestedInductive_withParams___redArg(v_type_5917_, v_nparams_5912_, v___f_5918_, v_a_5914_, v_a_5915_);
return v___x_5919_;
}
else
{
lean_object* v___x_5920_; 
lean_dec_ref(v_a_5915_);
lean_dec(v_types_5913_);
lean_dec(v_nparams_5912_);
v___x_5920_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_run___closed__2));
return v___x_5920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_ElimNestedInductive_run___boxed(lean_object* v_nparams_5921_, lean_object* v_types_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_){
_start:
{
lean_object* v_res_5925_; 
v_res_5925_ = l_Lean4Lean_ElimNestedInductive_run(v_nparams_5921_, v_types_5922_, v_a_5923_, v_a_5924_);
lean_dec_ref(v_a_5923_);
return v_res_5925_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0(lean_object* v_msg_5929_){
_start:
{
lean_object* v___f_5930_; lean_object* v___f_5931_; lean_object* v___f_5932_; lean_object* v___f_5933_; lean_object* v___f_5934_; lean_object* v___f_5935_; lean_object* v___f_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; 
v___f_5930_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__0));
v___f_5931_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__1));
v___f_5932_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__2));
v___f_5933_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__3));
v___f_5934_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__4));
v___f_5935_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__5));
v___f_5936_ = ((lean_object*)(l_panic___at___00Lean4Lean_ElimNestedInductive_Result_restoreCtorName_spec__0___closed__6));
v___x_5937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___f_5930_);
lean_ctor_set(v___x_5937_, 1, v___f_5931_);
v___x_5938_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5937_);
lean_ctor_set(v___x_5938_, 1, v___f_5932_);
lean_ctor_set(v___x_5938_, 2, v___f_5933_);
lean_ctor_set(v___x_5938_, 3, v___f_5934_);
lean_ctor_set(v___x_5938_, 4, v___f_5935_);
v___x_5939_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5938_);
lean_ctor_set(v___x_5939_, 1, v___f_5936_);
v___x_5940_ = ((lean_object*)(l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0___closed__0));
v___x_5941_ = l_instInhabitedOfMonad___redArg(v___x_5939_, v___x_5940_);
v___x_5942_ = lean_panic_fn_borrowed(v___x_5941_, v_msg_5929_);
lean_dec(v___x_5941_);
return v___x_5942_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___redArg(lean_object* v_mainName_5943_, lean_object* v_as_x27_5944_, lean_object* v_b_5945_){
_start:
{
if (lean_obj_tag(v_as_x27_5944_) == 0)
{
lean_dec(v_mainName_5943_);
return v_b_5945_;
}
else
{
lean_object* v_snd_5946_; lean_object* v_head_5947_; lean_object* v_tail_5948_; lean_object* v_fst_5949_; lean_object* v___x_5951_; uint8_t v_isShared_5952_; uint8_t v_isSharedCheck_5973_; 
v_snd_5946_ = lean_ctor_get(v_b_5945_, 1);
lean_inc(v_snd_5946_);
v_head_5947_ = lean_ctor_get(v_as_x27_5944_, 0);
v_tail_5948_ = lean_ctor_get(v_as_x27_5944_, 1);
v_fst_5949_ = lean_ctor_get(v_b_5945_, 0);
v_isSharedCheck_5973_ = !lean_is_exclusive(v_b_5945_);
if (v_isSharedCheck_5973_ == 0)
{
lean_object* v_unused_5974_; 
v_unused_5974_ = lean_ctor_get(v_b_5945_, 1);
lean_dec(v_unused_5974_);
v___x_5951_ = v_b_5945_;
v_isShared_5952_ = v_isSharedCheck_5973_;
goto v_resetjp_5950_;
}
else
{
lean_inc(v_fst_5949_);
lean_dec(v_b_5945_);
v___x_5951_ = lean_box(0);
v_isShared_5952_ = v_isSharedCheck_5973_;
goto v_resetjp_5950_;
}
v_resetjp_5950_:
{
lean_object* v_fst_5953_; lean_object* v_snd_5954_; lean_object* v___x_5956_; uint8_t v_isShared_5957_; uint8_t v_isSharedCheck_5972_; 
v_fst_5953_ = lean_ctor_get(v_snd_5946_, 0);
v_snd_5954_ = lean_ctor_get(v_snd_5946_, 1);
v_isSharedCheck_5972_ = !lean_is_exclusive(v_snd_5946_);
if (v_isSharedCheck_5972_ == 0)
{
v___x_5956_ = v_snd_5946_;
v_isShared_5957_ = v_isSharedCheck_5972_;
goto v_resetjp_5955_;
}
else
{
lean_inc(v_snd_5954_);
lean_inc(v_fst_5953_);
lean_dec(v_snd_5946_);
v___x_5956_ = lean_box(0);
v_isShared_5957_ = v_isSharedCheck_5972_;
goto v_resetjp_5955_;
}
v_resetjp_5955_:
{
lean_object* v_nextIdx_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; lean_object* v___x_5966_; 
v_nextIdx_5958_ = lean_unsigned_to_nat(1u);
lean_inc(v_head_5947_);
v___x_5959_ = l_Lean_mkRecName(v_head_5947_);
lean_inc(v_mainName_5943_);
v___x_5960_ = l_Lean_mkRecName(v_mainName_5943_);
lean_inc(v_snd_5954_);
v___x_5961_ = lean_name_append_index_after(v___x_5960_, v_snd_5954_);
v___x_5962_ = lean_nat_add(v_snd_5954_, v_nextIdx_5958_);
lean_dec(v_snd_5954_);
lean_inc(v___x_5959_);
v___x_5963_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v___x_5959_, v___x_5961_, v_fst_5953_);
v___x_5964_ = lean_array_push(v_fst_5949_, v___x_5959_);
if (v_isShared_5957_ == 0)
{
lean_ctor_set(v___x_5956_, 1, v___x_5962_);
lean_ctor_set(v___x_5956_, 0, v___x_5963_);
v___x_5966_ = v___x_5956_;
goto v_reusejp_5965_;
}
else
{
lean_object* v_reuseFailAlloc_5971_; 
v_reuseFailAlloc_5971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5971_, 0, v___x_5963_);
lean_ctor_set(v_reuseFailAlloc_5971_, 1, v___x_5962_);
v___x_5966_ = v_reuseFailAlloc_5971_;
goto v_reusejp_5965_;
}
v_reusejp_5965_:
{
lean_object* v___x_5968_; 
if (v_isShared_5952_ == 0)
{
lean_ctor_set(v___x_5951_, 1, v___x_5966_);
lean_ctor_set(v___x_5951_, 0, v___x_5964_);
v___x_5968_ = v___x_5951_;
goto v_reusejp_5967_;
}
else
{
lean_object* v_reuseFailAlloc_5970_; 
v_reuseFailAlloc_5970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5970_, 0, v___x_5964_);
lean_ctor_set(v_reuseFailAlloc_5970_, 1, v___x_5966_);
v___x_5968_ = v_reuseFailAlloc_5970_;
goto v_reusejp_5967_;
}
v_reusejp_5967_:
{
v_as_x27_5944_ = v_tail_5948_;
v_b_5945_ = v___x_5968_;
goto _start;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___redArg___boxed(lean_object* v_mainName_5975_, lean_object* v_as_x27_5976_, lean_object* v_b_5977_){
_start:
{
lean_object* v_res_5978_; 
v_res_5978_ = l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___redArg(v_mainName_5975_, v_as_x27_5976_, v_b_5977_);
lean_dec(v_as_x27_5976_);
return v_res_5978_;
}
}
static lean_object* _init_l_Lean4Lean_mkAuxRecNameMap___closed__1(void){
_start:
{
lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
v___x_5980_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_5981_ = lean_unsigned_to_nat(59u);
v___x_5982_ = lean_unsigned_to_nat(708u);
v___x_5983_ = ((lean_object*)(l_Lean4Lean_mkAuxRecNameMap___closed__0));
v___x_5984_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_5985_ = l_mkPanicMessageWithDecl(v___x_5984_, v___x_5983_, v___x_5982_, v___x_5981_, v___x_5980_);
return v___x_5985_;
}
}
static lean_object* _init_l_Lean4Lean_mkAuxRecNameMap___closed__3(void){
_start:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5987_ = ((lean_object*)(l_Lean4Lean_mkAuxRecNameMap___closed__2));
v___x_5988_ = lean_unsigned_to_nat(2u);
v___x_5989_ = lean_unsigned_to_nat(710u);
v___x_5990_ = ((lean_object*)(l_Lean4Lean_mkAuxRecNameMap___closed__0));
v___x_5991_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_5992_ = l_mkPanicMessageWithDecl(v___x_5991_, v___x_5990_, v___x_5989_, v___x_5988_, v___x_5987_);
return v___x_5992_;
}
}
static lean_object* _init_l_Lean4Lean_mkAuxRecNameMap___closed__7(void){
_start:
{
lean_object* v___x_6001_; lean_object* v___x_6002_; lean_object* v___x_6003_; lean_object* v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; 
v___x_6001_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_6002_ = lean_unsigned_to_nat(31u);
v___x_6003_ = lean_unsigned_to_nat(705u);
v___x_6004_ = ((lean_object*)(l_Lean4Lean_mkAuxRecNameMap___closed__0));
v___x_6005_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_6006_ = l_mkPanicMessageWithDecl(v___x_6005_, v___x_6004_, v___x_6003_, v___x_6002_, v___x_6001_);
return v___x_6006_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_mkAuxRecNameMap(lean_object* v_env_x27_6007_, lean_object* v_types_6008_){
_start:
{
if (lean_obj_tag(v_types_6008_) == 1)
{
lean_object* v_head_6012_; lean_object* v_name_6013_; lean_object* v___x_6014_; 
v_head_6012_ = lean_ctor_get(v_types_6008_, 0);
v_name_6013_ = lean_ctor_get(v_head_6012_, 0);
lean_inc_n(v_name_6013_, 2);
v___x_6014_ = lean_environment_find(v_env_x27_6007_, v_name_6013_);
if (lean_obj_tag(v___x_6014_) == 1)
{
lean_object* v_val_6015_; 
v_val_6015_ = lean_ctor_get(v___x_6014_, 0);
lean_inc(v_val_6015_);
lean_dec_ref(v___x_6014_);
if (lean_obj_tag(v_val_6015_) == 5)
{
lean_object* v_val_6016_; lean_object* v_all_6017_; lean_object* v_ntypes_6018_; lean_object* v___x_6019_; uint8_t v___x_6020_; 
v_val_6016_ = lean_ctor_get(v_val_6015_, 0);
lean_inc_ref(v_val_6016_);
lean_dec_ref(v_val_6015_);
v_all_6017_ = lean_ctor_get(v_val_6016_, 3);
lean_inc(v_all_6017_);
lean_dec_ref(v_val_6016_);
v_ntypes_6018_ = l_List_lengthTR___redArg(v_types_6008_);
lean_dec_ref(v_types_6008_);
v___x_6019_ = l_List_lengthTR___redArg(v_all_6017_);
v___x_6020_ = lean_nat_dec_lt(v_ntypes_6018_, v___x_6019_);
lean_dec(v___x_6019_);
if (v___x_6020_ == 0)
{
lean_object* v___x_6021_; lean_object* v___x_6022_; 
lean_dec(v_ntypes_6018_);
lean_dec(v_all_6017_);
lean_dec(v_name_6013_);
v___x_6021_ = lean_obj_once(&l_Lean4Lean_mkAuxRecNameMap___closed__3, &l_Lean4Lean_mkAuxRecNameMap___closed__3_once, _init_l_Lean4Lean_mkAuxRecNameMap___closed__3);
v___x_6022_ = l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0(v___x_6021_);
return v___x_6022_;
}
else
{
lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; lean_object* v_snd_6026_; lean_object* v_fst_6027_; lean_object* v_fst_6028_; lean_object* v___x_6030_; uint8_t v_isShared_6031_; uint8_t v_isSharedCheck_6036_; 
v___x_6023_ = l_List_drop___redArg(v_ntypes_6018_, v_all_6017_);
lean_dec(v_all_6017_);
v___x_6024_ = ((lean_object*)(l_Lean4Lean_mkAuxRecNameMap___closed__6));
v___x_6025_ = l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___redArg(v_name_6013_, v___x_6023_, v___x_6024_);
lean_dec(v___x_6023_);
v_snd_6026_ = lean_ctor_get(v___x_6025_, 1);
lean_inc(v_snd_6026_);
v_fst_6027_ = lean_ctor_get(v___x_6025_, 0);
lean_inc(v_fst_6027_);
lean_dec_ref(v___x_6025_);
v_fst_6028_ = lean_ctor_get(v_snd_6026_, 0);
v_isSharedCheck_6036_ = !lean_is_exclusive(v_snd_6026_);
if (v_isSharedCheck_6036_ == 0)
{
lean_object* v_unused_6037_; 
v_unused_6037_ = lean_ctor_get(v_snd_6026_, 1);
lean_dec(v_unused_6037_);
v___x_6030_ = v_snd_6026_;
v_isShared_6031_ = v_isSharedCheck_6036_;
goto v_resetjp_6029_;
}
else
{
lean_inc(v_fst_6028_);
lean_dec(v_snd_6026_);
v___x_6030_ = lean_box(0);
v_isShared_6031_ = v_isSharedCheck_6036_;
goto v_resetjp_6029_;
}
v_resetjp_6029_:
{
lean_object* v___x_6032_; lean_object* v___x_6034_; 
v___x_6032_ = lean_array_to_list(v_fst_6027_);
if (v_isShared_6031_ == 0)
{
lean_ctor_set(v___x_6030_, 1, v_fst_6028_);
lean_ctor_set(v___x_6030_, 0, v___x_6032_);
v___x_6034_ = v___x_6030_;
goto v_reusejp_6033_;
}
else
{
lean_object* v_reuseFailAlloc_6035_; 
v_reuseFailAlloc_6035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6035_, 0, v___x_6032_);
lean_ctor_set(v_reuseFailAlloc_6035_, 1, v_fst_6028_);
v___x_6034_ = v_reuseFailAlloc_6035_;
goto v_reusejp_6033_;
}
v_reusejp_6033_:
{
return v___x_6034_;
}
}
}
}
else
{
lean_dec(v_val_6015_);
lean_dec(v_name_6013_);
lean_dec_ref(v_types_6008_);
goto v___jp_6009_;
}
}
else
{
lean_dec(v___x_6014_);
lean_dec(v_name_6013_);
lean_dec_ref(v_types_6008_);
goto v___jp_6009_;
}
}
else
{
lean_object* v___x_6038_; lean_object* v___x_6039_; 
lean_dec(v_types_6008_);
lean_dec_ref(v_env_x27_6007_);
v___x_6038_ = lean_obj_once(&l_Lean4Lean_mkAuxRecNameMap___closed__7, &l_Lean4Lean_mkAuxRecNameMap___closed__7_once, _init_l_Lean4Lean_mkAuxRecNameMap___closed__7);
v___x_6039_ = l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0(v___x_6038_);
return v___x_6039_;
}
v___jp_6009_:
{
lean_object* v___x_6010_; lean_object* v___x_6011_; 
v___x_6010_ = lean_obj_once(&l_Lean4Lean_mkAuxRecNameMap___closed__1, &l_Lean4Lean_mkAuxRecNameMap___closed__1_once, _init_l_Lean4Lean_mkAuxRecNameMap___closed__1);
v___x_6011_ = l_panic___at___00Lean4Lean_mkAuxRecNameMap_spec__0(v___x_6010_);
return v___x_6011_;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1(lean_object* v_mainName_6040_, lean_object* v_as_6041_, lean_object* v_as_x27_6042_, lean_object* v_b_6043_, lean_object* v_a_6044_){
_start:
{
lean_object* v___x_6045_; 
v___x_6045_ = l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___redArg(v_mainName_6040_, v_as_x27_6042_, v_b_6043_);
return v___x_6045_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1___boxed(lean_object* v_mainName_6046_, lean_object* v_as_6047_, lean_object* v_as_x27_6048_, lean_object* v_b_6049_, lean_object* v_a_6050_){
_start:
{
lean_object* v_res_6051_; 
v_res_6051_ = l_List_forIn_x27_loop___at___00Lean4Lean_mkAuxRecNameMap_spec__1(v_mainName_6046_, v_as_6047_, v_as_x27_6048_, v_b_6049_, v_a_6050_);
lean_dec(v_as_x27_6048_);
lean_dec(v_as_6047_);
return v_res_6051_;
}
}
static lean_object* _init_l_panic___at___00Lean4Lean_Environment_addInductive_spec__1___closed__0(void){
_start:
{
lean_object* v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; 
v___x_6052_ = lean_box(0);
v___x_6053_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_instMonadNameGeneratorM___closed__12));
v___x_6054_ = l_instInhabitedOfMonad___redArg(v___x_6053_, v___x_6052_);
return v___x_6054_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(lean_object* v_msg_6055_, lean_object* v___y_6056_){
_start:
{
lean_object* v___x_6057_; lean_object* v___x_6939__overap_6058_; lean_object* v___x_6059_; 
v___x_6057_ = lean_obj_once(&l_panic___at___00Lean4Lean_Environment_addInductive_spec__1___closed__0, &l_panic___at___00Lean4Lean_Environment_addInductive_spec__1___closed__0_once, _init_l_panic___at___00Lean4Lean_Environment_addInductive_spec__1___closed__0);
v___x_6939__overap_6058_ = lean_panic_fn_borrowed(v___x_6057_, v_msg_6055_);
v___x_6059_ = lean_apply_1(v___x_6939__overap_6058_, v___y_6056_);
return v___x_6059_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3(lean_object* v___x_6060_, lean_object* v_a_6061_, lean_object* v_snd_6062_, lean_object* v___x_6063_, lean_object* v_recName_6064_, lean_object* v_x_6065_, lean_object* v_x_6066_, lean_object* v___y_6067_){
_start:
{
if (lean_obj_tag(v_x_6065_) == 0)
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
lean_dec(v_snd_6062_);
lean_dec_ref(v_a_6061_);
lean_dec_ref(v___x_6060_);
v___x_6068_ = l_List_reverse___redArg(v_x_6066_);
v___x_6069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6068_);
lean_ctor_set(v___x_6069_, 1, v___y_6067_);
v___x_6070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6069_);
return v___x_6070_;
}
else
{
lean_object* v_head_6071_; lean_object* v_tail_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6095_; 
v_head_6071_ = lean_ctor_get(v_x_6065_, 0);
v_tail_6072_ = lean_ctor_get(v_x_6065_, 1);
v_isSharedCheck_6095_ = !lean_is_exclusive(v_x_6065_);
if (v_isSharedCheck_6095_ == 0)
{
v___x_6074_ = v_x_6065_;
v_isShared_6075_ = v_isSharedCheck_6095_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_tail_6072_);
lean_inc(v_head_6071_);
lean_dec(v_x_6065_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6095_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v_ctor_6076_; lean_object* v_nfields_6077_; lean_object* v_rhs_6078_; lean_object* v___x_6080_; uint8_t v_isShared_6081_; uint8_t v_isSharedCheck_6094_; 
v_ctor_6076_ = lean_ctor_get(v_head_6071_, 0);
v_nfields_6077_ = lean_ctor_get(v_head_6071_, 1);
v_rhs_6078_ = lean_ctor_get(v_head_6071_, 2);
v_isSharedCheck_6094_ = !lean_is_exclusive(v_head_6071_);
if (v_isSharedCheck_6094_ == 0)
{
v___x_6080_ = v_head_6071_;
v_isShared_6081_ = v_isSharedCheck_6094_;
goto v_resetjp_6079_;
}
else
{
lean_inc(v_rhs_6078_);
lean_inc(v_nfields_6077_);
lean_inc(v_ctor_6076_);
lean_dec(v_head_6071_);
v___x_6080_ = lean_box(0);
v_isShared_6081_ = v_isSharedCheck_6094_;
goto v_resetjp_6079_;
}
v_resetjp_6079_:
{
lean_object* v___x_6082_; lean_object* v___y_6084_; uint8_t v___x_6092_; 
lean_inc(v_snd_6062_);
lean_inc_ref(v_a_6061_);
lean_inc_ref(v___x_6060_);
v___x_6082_ = l_Lean4Lean_ElimNestedInductive_Result_restoreNested(v___x_6060_, v_a_6061_, v_rhs_6078_, v_snd_6062_);
v___x_6092_ = lean_name_eq(v___x_6063_, v_recName_6064_);
if (v___x_6092_ == 0)
{
lean_object* v___x_6093_; 
lean_inc_ref(v_a_6061_);
v___x_6093_ = l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName(v___x_6060_, v_a_6061_, v_ctor_6076_);
v___y_6084_ = v___x_6093_;
goto v___jp_6083_;
}
else
{
v___y_6084_ = v_ctor_6076_;
goto v___jp_6083_;
}
v___jp_6083_:
{
lean_object* v___x_6086_; 
if (v_isShared_6081_ == 0)
{
lean_ctor_set(v___x_6080_, 2, v___x_6082_);
lean_ctor_set(v___x_6080_, 0, v___y_6084_);
v___x_6086_ = v___x_6080_;
goto v_reusejp_6085_;
}
else
{
lean_object* v_reuseFailAlloc_6091_; 
v_reuseFailAlloc_6091_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6091_, 0, v___y_6084_);
lean_ctor_set(v_reuseFailAlloc_6091_, 1, v_nfields_6077_);
lean_ctor_set(v_reuseFailAlloc_6091_, 2, v___x_6082_);
v___x_6086_ = v_reuseFailAlloc_6091_;
goto v_reusejp_6085_;
}
v_reusejp_6085_:
{
lean_object* v___x_6088_; 
if (v_isShared_6075_ == 0)
{
lean_ctor_set(v___x_6074_, 1, v_x_6066_);
lean_ctor_set(v___x_6074_, 0, v___x_6086_);
v___x_6088_ = v___x_6074_;
goto v_reusejp_6087_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v___x_6086_);
lean_ctor_set(v_reuseFailAlloc_6090_, 1, v_x_6066_);
v___x_6088_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6087_;
}
v_reusejp_6087_:
{
v_x_6065_ = v_tail_6072_;
v_x_6066_ = v___x_6088_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3___boxed(lean_object* v___x_6096_, lean_object* v_a_6097_, lean_object* v_snd_6098_, lean_object* v___x_6099_, lean_object* v_recName_6100_, lean_object* v_x_6101_, lean_object* v_x_6102_, lean_object* v___y_6103_){
_start:
{
lean_object* v_res_6104_; 
v_res_6104_ = l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3(v___x_6096_, v_a_6097_, v_snd_6098_, v___x_6099_, v_recName_6100_, v_x_6101_, v_x_6102_, v___y_6103_);
lean_dec(v_recName_6100_);
lean_dec(v___x_6099_);
return v_res_6104_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(lean_object* v_t_6105_, lean_object* v_k_6106_, lean_object* v_fallback_6107_){
_start:
{
if (lean_obj_tag(v_t_6105_) == 0)
{
lean_object* v_k_6108_; lean_object* v_v_6109_; lean_object* v_l_6110_; lean_object* v_r_6111_; uint8_t v___x_6112_; 
v_k_6108_ = lean_ctor_get(v_t_6105_, 1);
v_v_6109_ = lean_ctor_get(v_t_6105_, 2);
v_l_6110_ = lean_ctor_get(v_t_6105_, 3);
v_r_6111_ = lean_ctor_get(v_t_6105_, 4);
v___x_6112_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_6106_, v_k_6108_);
switch(v___x_6112_)
{
case 0:
{
v_t_6105_ = v_l_6110_;
goto _start;
}
case 1:
{
lean_inc(v_v_6109_);
return v_v_6109_;
}
default: 
{
v_t_6105_ = v_r_6111_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_6107_);
return v_fallback_6107_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg___boxed(lean_object* v_t_6115_, lean_object* v_k_6116_, lean_object* v_fallback_6117_){
_start:
{
lean_object* v_res_6118_; 
v_res_6118_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(v_t_6115_, v_k_6116_, v_fallback_6117_);
lean_dec(v_fallback_6117_);
lean_dec(v_k_6116_);
lean_dec(v_t_6115_);
return v_res_6118_;
}
}
static lean_object* _init_l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1(void){
_start:
{
lean_object* v___x_6120_; lean_object* v___x_6121_; lean_object* v___x_6122_; lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; 
v___x_6120_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_6121_ = lean_unsigned_to_nat(56u);
v___x_6122_ = lean_unsigned_to_nat(736u);
v___x_6123_ = ((lean_object*)(l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__0));
v___x_6124_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_6125_ = l_mkPanicMessageWithDecl(v___x_6124_, v___x_6123_, v___x_6122_, v___x_6121_, v___x_6120_);
return v___x_6125_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7(lean_object* v_snd_6126_, lean_object* v_a_6127_, lean_object* v___x_6128_, uint8_t v_allowPrimitive_6129_, lean_object* v___x_6130_, lean_object* v_as_6131_, lean_object* v___y_6132_){
_start:
{
if (lean_obj_tag(v_as_6131_) == 0)
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
lean_dec(v___x_6130_);
lean_dec_ref(v___x_6128_);
lean_dec_ref(v_a_6127_);
lean_dec(v_snd_6126_);
v___x_6133_ = lean_box(0);
v___x_6134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6134_, 0, v___x_6133_);
lean_ctor_set(v___x_6134_, 1, v___y_6132_);
v___x_6135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6134_);
return v___x_6135_;
}
else
{
lean_object* v_head_6136_; lean_object* v_tail_6137_; lean_object* v___y_6139_; lean_object* v___x_6145_; lean_object* v___x_6146_; 
v_head_6136_ = lean_ctor_get(v_as_6131_, 0);
lean_inc_n(v_head_6136_, 2);
v_tail_6137_ = lean_ctor_get(v_as_6131_, 1);
lean_inc(v_tail_6137_);
lean_dec_ref(v_as_6131_);
v___x_6145_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(v_snd_6126_, v_head_6136_, v_head_6136_);
lean_inc_ref(v_a_6127_);
v___x_6146_ = lean_environment_find(v_a_6127_, v_head_6136_);
if (lean_obj_tag(v___x_6146_) == 1)
{
lean_object* v_val_6147_; 
v_val_6147_ = lean_ctor_get(v___x_6146_, 0);
lean_inc(v_val_6147_);
lean_dec_ref(v___x_6146_);
if (lean_obj_tag(v_val_6147_) == 7)
{
lean_object* v_val_6148_; lean_object* v___x_6150_; uint8_t v_isShared_6151_; uint8_t v_isSharedCheck_6198_; 
v_val_6148_ = lean_ctor_get(v_val_6147_, 0);
v_isSharedCheck_6198_ = !lean_is_exclusive(v_val_6147_);
if (v_isSharedCheck_6198_ == 0)
{
v___x_6150_ = v_val_6147_;
v_isShared_6151_ = v_isSharedCheck_6198_;
goto v_resetjp_6149_;
}
else
{
lean_inc(v_val_6148_);
lean_dec(v_val_6147_);
v___x_6150_ = lean_box(0);
v_isShared_6151_ = v_isSharedCheck_6198_;
goto v_resetjp_6149_;
}
v_resetjp_6149_:
{
lean_object* v_toConstantVal_6152_; lean_object* v_numParams_6153_; lean_object* v_numIndices_6154_; lean_object* v_numMotives_6155_; lean_object* v_numMinors_6156_; lean_object* v_rules_6157_; uint8_t v_k_6158_; uint8_t v_isUnsafe_6159_; lean_object* v___x_6161_; uint8_t v_isShared_6162_; uint8_t v_isSharedCheck_6196_; 
v_toConstantVal_6152_ = lean_ctor_get(v_val_6148_, 0);
v_numParams_6153_ = lean_ctor_get(v_val_6148_, 2);
v_numIndices_6154_ = lean_ctor_get(v_val_6148_, 3);
v_numMotives_6155_ = lean_ctor_get(v_val_6148_, 4);
v_numMinors_6156_ = lean_ctor_get(v_val_6148_, 5);
v_rules_6157_ = lean_ctor_get(v_val_6148_, 6);
v_k_6158_ = lean_ctor_get_uint8(v_val_6148_, sizeof(void*)*7);
v_isUnsafe_6159_ = lean_ctor_get_uint8(v_val_6148_, sizeof(void*)*7 + 1);
v_isSharedCheck_6196_ = !lean_is_exclusive(v_val_6148_);
if (v_isSharedCheck_6196_ == 0)
{
lean_object* v_unused_6197_; 
v_unused_6197_ = lean_ctor_get(v_val_6148_, 1);
lean_dec(v_unused_6197_);
v___x_6161_ = v_val_6148_;
v_isShared_6162_ = v_isSharedCheck_6196_;
goto v_resetjp_6160_;
}
else
{
lean_inc(v_rules_6157_);
lean_inc(v_numMinors_6156_);
lean_inc(v_numMotives_6155_);
lean_inc(v_numIndices_6154_);
lean_inc(v_numParams_6153_);
lean_inc(v_toConstantVal_6152_);
lean_dec(v_val_6148_);
v___x_6161_ = lean_box(0);
v_isShared_6162_ = v_isSharedCheck_6196_;
goto v_resetjp_6160_;
}
v_resetjp_6160_:
{
lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v_a_6165_; lean_object* v_fst_6166_; lean_object* v_snd_6167_; lean_object* v___x_6168_; 
v___x_6163_ = lean_box(0);
lean_inc(v_snd_6126_);
lean_inc_ref(v_a_6127_);
lean_inc_ref(v___x_6128_);
v___x_6164_ = l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3(v___x_6128_, v_a_6127_, v_snd_6126_, v___x_6145_, v_head_6136_, v_rules_6157_, v___x_6163_, v___y_6132_);
lean_dec(v_head_6136_);
v_a_6165_ = lean_ctor_get(v___x_6164_, 0);
lean_inc(v_a_6165_);
lean_dec_ref(v___x_6164_);
v_fst_6166_ = lean_ctor_get(v_a_6165_, 0);
lean_inc(v_fst_6166_);
v_snd_6167_ = lean_ctor_get(v_a_6165_, 1);
lean_inc_n(v_snd_6167_, 2);
lean_dec(v_a_6165_);
lean_inc(v___x_6145_);
v___x_6168_ = l_Lean_Kernel_Environment_checkName(v_snd_6167_, v___x_6145_, v_allowPrimitive_6129_);
if (lean_obj_tag(v___x_6168_) == 0)
{
lean_object* v_a_6169_; lean_object* v___x_6171_; uint8_t v_isShared_6172_; uint8_t v_isSharedCheck_6176_; 
lean_dec(v_snd_6167_);
lean_dec(v_fst_6166_);
lean_del_object(v___x_6161_);
lean_dec(v_numMinors_6156_);
lean_dec(v_numMotives_6155_);
lean_dec(v_numIndices_6154_);
lean_dec(v_numParams_6153_);
lean_dec_ref(v_toConstantVal_6152_);
lean_del_object(v___x_6150_);
lean_dec(v___x_6145_);
lean_dec(v_tail_6137_);
lean_dec(v___x_6130_);
lean_dec_ref(v___x_6128_);
lean_dec_ref(v_a_6127_);
lean_dec(v_snd_6126_);
v_a_6169_ = lean_ctor_get(v___x_6168_, 0);
v_isSharedCheck_6176_ = !lean_is_exclusive(v___x_6168_);
if (v_isSharedCheck_6176_ == 0)
{
v___x_6171_ = v___x_6168_;
v_isShared_6172_ = v_isSharedCheck_6176_;
goto v_resetjp_6170_;
}
else
{
lean_inc(v_a_6169_);
lean_dec(v___x_6168_);
v___x_6171_ = lean_box(0);
v_isShared_6172_ = v_isSharedCheck_6176_;
goto v_resetjp_6170_;
}
v_resetjp_6170_:
{
lean_object* v___x_6174_; 
if (v_isShared_6172_ == 0)
{
v___x_6174_ = v___x_6171_;
goto v_reusejp_6173_;
}
else
{
lean_object* v_reuseFailAlloc_6175_; 
v_reuseFailAlloc_6175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6175_, 0, v_a_6169_);
v___x_6174_ = v_reuseFailAlloc_6175_;
goto v_reusejp_6173_;
}
v_reusejp_6173_:
{
return v___x_6174_;
}
}
}
else
{
lean_object* v_levelParams_6177_; lean_object* v_type_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6194_; 
lean_dec_ref(v___x_6168_);
v_levelParams_6177_ = lean_ctor_get(v_toConstantVal_6152_, 1);
v_type_6178_ = lean_ctor_get(v_toConstantVal_6152_, 2);
v_isSharedCheck_6194_ = !lean_is_exclusive(v_toConstantVal_6152_);
if (v_isSharedCheck_6194_ == 0)
{
lean_object* v_unused_6195_; 
v_unused_6195_ = lean_ctor_get(v_toConstantVal_6152_, 0);
lean_dec(v_unused_6195_);
v___x_6180_ = v_toConstantVal_6152_;
v_isShared_6181_ = v_isSharedCheck_6194_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_type_6178_);
lean_inc(v_levelParams_6177_);
lean_dec(v_toConstantVal_6152_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6194_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v___x_6182_; lean_object* v___x_6184_; 
lean_inc(v_snd_6126_);
lean_inc_ref(v_a_6127_);
lean_inc_ref(v___x_6128_);
v___x_6182_ = l_Lean4Lean_ElimNestedInductive_Result_restoreNested(v___x_6128_, v_a_6127_, v_type_6178_, v_snd_6126_);
if (v_isShared_6181_ == 0)
{
lean_ctor_set(v___x_6180_, 2, v___x_6182_);
lean_ctor_set(v___x_6180_, 0, v___x_6145_);
v___x_6184_ = v___x_6180_;
goto v_reusejp_6183_;
}
else
{
lean_object* v_reuseFailAlloc_6193_; 
v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6145_);
lean_ctor_set(v_reuseFailAlloc_6193_, 1, v_levelParams_6177_);
lean_ctor_set(v_reuseFailAlloc_6193_, 2, v___x_6182_);
v___x_6184_ = v_reuseFailAlloc_6193_;
goto v_reusejp_6183_;
}
v_reusejp_6183_:
{
lean_object* v___x_6186_; 
lean_inc(v___x_6130_);
if (v_isShared_6162_ == 0)
{
lean_ctor_set(v___x_6161_, 6, v_fst_6166_);
lean_ctor_set(v___x_6161_, 1, v___x_6130_);
lean_ctor_set(v___x_6161_, 0, v___x_6184_);
v___x_6186_ = v___x_6161_;
goto v_reusejp_6185_;
}
else
{
lean_object* v_reuseFailAlloc_6192_; 
v_reuseFailAlloc_6192_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6184_);
lean_ctor_set(v_reuseFailAlloc_6192_, 1, v___x_6130_);
lean_ctor_set(v_reuseFailAlloc_6192_, 2, v_numParams_6153_);
lean_ctor_set(v_reuseFailAlloc_6192_, 3, v_numIndices_6154_);
lean_ctor_set(v_reuseFailAlloc_6192_, 4, v_numMotives_6155_);
lean_ctor_set(v_reuseFailAlloc_6192_, 5, v_numMinors_6156_);
lean_ctor_set(v_reuseFailAlloc_6192_, 6, v_fst_6166_);
lean_ctor_set_uint8(v_reuseFailAlloc_6192_, sizeof(void*)*7, v_k_6158_);
lean_ctor_set_uint8(v_reuseFailAlloc_6192_, sizeof(void*)*7 + 1, v_isUnsafe_6159_);
v___x_6186_ = v_reuseFailAlloc_6192_;
goto v_reusejp_6185_;
}
v_reusejp_6185_:
{
lean_object* v___x_6188_; 
if (v_isShared_6151_ == 0)
{
lean_ctor_set(v___x_6150_, 0, v___x_6186_);
v___x_6188_ = v___x_6150_;
goto v_reusejp_6187_;
}
else
{
lean_object* v_reuseFailAlloc_6191_; 
v_reuseFailAlloc_6191_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6191_, 0, v___x_6186_);
v___x_6188_ = v_reuseFailAlloc_6191_;
goto v_reusejp_6187_;
}
v_reusejp_6187_:
{
lean_object* v___x_6189_; 
v___x_6189_ = lean_environment_add(v_snd_6167_, v___x_6188_);
v_as_6131_ = v_tail_6137_;
v___y_6132_ = v___x_6189_;
goto _start;
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
lean_dec(v_val_6147_);
lean_dec(v___x_6145_);
lean_dec(v_head_6136_);
v___y_6139_ = v___y_6132_;
goto v___jp_6138_;
}
}
else
{
lean_dec(v___x_6146_);
lean_dec(v___x_6145_);
lean_dec(v_head_6136_);
v___y_6139_ = v___y_6132_;
goto v___jp_6138_;
}
v___jp_6138_:
{
lean_object* v___x_6140_; lean_object* v___x_6141_; 
v___x_6140_ = lean_obj_once(&l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1, &l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1_once, _init_l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1);
v___x_6141_ = l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(v___x_6140_, v___y_6139_);
if (lean_obj_tag(v___x_6141_) == 0)
{
lean_dec(v_tail_6137_);
lean_dec(v___x_6130_);
lean_dec_ref(v___x_6128_);
lean_dec_ref(v_a_6127_);
lean_dec(v_snd_6126_);
return v___x_6141_;
}
else
{
lean_object* v_a_6142_; lean_object* v_snd_6143_; 
v_a_6142_ = lean_ctor_get(v___x_6141_, 0);
lean_inc(v_a_6142_);
lean_dec_ref(v___x_6141_);
v_snd_6143_ = lean_ctor_get(v_a_6142_, 1);
lean_inc(v_snd_6143_);
lean_dec(v_a_6142_);
v_as_6131_ = v_tail_6137_;
v___y_6132_ = v_snd_6143_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___boxed(lean_object* v_snd_6199_, lean_object* v_a_6200_, lean_object* v___x_6201_, lean_object* v_allowPrimitive_6202_, lean_object* v___x_6203_, lean_object* v_as_6204_, lean_object* v___y_6205_){
_start:
{
uint8_t v_allowPrimitive_boxed_6206_; lean_object* v_res_6207_; 
v_allowPrimitive_boxed_6206_ = lean_unbox(v_allowPrimitive_6202_);
v_res_6207_ = l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7(v_snd_6199_, v_a_6200_, v___x_6201_, v_allowPrimitive_boxed_6206_, v___x_6203_, v_as_6204_, v___y_6205_);
return v_res_6207_;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean4Lean_Environment_addInductive_spec__6(lean_object* v_snd_6208_, lean_object* v___x_6209_, lean_object* v_a_6210_, uint8_t v_allowPrimitive_6211_, lean_object* v___x_6212_, lean_object* v_as_6213_, lean_object* v___y_6214_){
_start:
{
if (lean_obj_tag(v_as_6213_) == 0)
{
lean_object* v___x_6215_; lean_object* v___x_6216_; lean_object* v___x_6217_; 
lean_dec(v___x_6212_);
lean_dec_ref(v_a_6210_);
lean_dec_ref(v___x_6209_);
lean_dec(v_snd_6208_);
v___x_6215_ = lean_box(0);
v___x_6216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6216_, 0, v___x_6215_);
lean_ctor_set(v___x_6216_, 1, v___y_6214_);
v___x_6217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6217_, 0, v___x_6216_);
return v___x_6217_;
}
else
{
lean_object* v_head_6218_; lean_object* v_tail_6219_; lean_object* v___y_6221_; lean_object* v___x_6227_; lean_object* v___x_6228_; 
v_head_6218_ = lean_ctor_get(v_as_6213_, 0);
lean_inc_n(v_head_6218_, 2);
v_tail_6219_ = lean_ctor_get(v_as_6213_, 1);
lean_inc(v_tail_6219_);
lean_dec_ref(v_as_6213_);
v___x_6227_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(v_snd_6208_, v_head_6218_, v_head_6218_);
lean_inc_ref(v_a_6210_);
v___x_6228_ = lean_environment_find(v_a_6210_, v_head_6218_);
if (lean_obj_tag(v___x_6228_) == 1)
{
lean_object* v_val_6229_; 
v_val_6229_ = lean_ctor_get(v___x_6228_, 0);
lean_inc(v_val_6229_);
lean_dec_ref(v___x_6228_);
if (lean_obj_tag(v_val_6229_) == 7)
{
lean_object* v_val_6230_; lean_object* v___x_6232_; uint8_t v_isShared_6233_; uint8_t v_isSharedCheck_6280_; 
v_val_6230_ = lean_ctor_get(v_val_6229_, 0);
v_isSharedCheck_6280_ = !lean_is_exclusive(v_val_6229_);
if (v_isSharedCheck_6280_ == 0)
{
v___x_6232_ = v_val_6229_;
v_isShared_6233_ = v_isSharedCheck_6280_;
goto v_resetjp_6231_;
}
else
{
lean_inc(v_val_6230_);
lean_dec(v_val_6229_);
v___x_6232_ = lean_box(0);
v_isShared_6233_ = v_isSharedCheck_6280_;
goto v_resetjp_6231_;
}
v_resetjp_6231_:
{
lean_object* v_toConstantVal_6234_; lean_object* v_numParams_6235_; lean_object* v_numIndices_6236_; lean_object* v_numMotives_6237_; lean_object* v_numMinors_6238_; lean_object* v_rules_6239_; uint8_t v_k_6240_; uint8_t v_isUnsafe_6241_; lean_object* v___x_6243_; uint8_t v_isShared_6244_; uint8_t v_isSharedCheck_6278_; 
v_toConstantVal_6234_ = lean_ctor_get(v_val_6230_, 0);
v_numParams_6235_ = lean_ctor_get(v_val_6230_, 2);
v_numIndices_6236_ = lean_ctor_get(v_val_6230_, 3);
v_numMotives_6237_ = lean_ctor_get(v_val_6230_, 4);
v_numMinors_6238_ = lean_ctor_get(v_val_6230_, 5);
v_rules_6239_ = lean_ctor_get(v_val_6230_, 6);
v_k_6240_ = lean_ctor_get_uint8(v_val_6230_, sizeof(void*)*7);
v_isUnsafe_6241_ = lean_ctor_get_uint8(v_val_6230_, sizeof(void*)*7 + 1);
v_isSharedCheck_6278_ = !lean_is_exclusive(v_val_6230_);
if (v_isSharedCheck_6278_ == 0)
{
lean_object* v_unused_6279_; 
v_unused_6279_ = lean_ctor_get(v_val_6230_, 1);
lean_dec(v_unused_6279_);
v___x_6243_ = v_val_6230_;
v_isShared_6244_ = v_isSharedCheck_6278_;
goto v_resetjp_6242_;
}
else
{
lean_inc(v_rules_6239_);
lean_inc(v_numMinors_6238_);
lean_inc(v_numMotives_6237_);
lean_inc(v_numIndices_6236_);
lean_inc(v_numParams_6235_);
lean_inc(v_toConstantVal_6234_);
lean_dec(v_val_6230_);
v___x_6243_ = lean_box(0);
v_isShared_6244_ = v_isSharedCheck_6278_;
goto v_resetjp_6242_;
}
v_resetjp_6242_:
{
lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v_a_6247_; lean_object* v_fst_6248_; lean_object* v_snd_6249_; lean_object* v___x_6250_; 
v___x_6245_ = lean_box(0);
lean_inc(v_snd_6208_);
lean_inc_ref(v_a_6210_);
lean_inc_ref(v___x_6209_);
v___x_6246_ = l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3(v___x_6209_, v_a_6210_, v_snd_6208_, v___x_6227_, v_head_6218_, v_rules_6239_, v___x_6245_, v___y_6214_);
lean_dec(v_head_6218_);
v_a_6247_ = lean_ctor_get(v___x_6246_, 0);
lean_inc(v_a_6247_);
lean_dec_ref(v___x_6246_);
v_fst_6248_ = lean_ctor_get(v_a_6247_, 0);
lean_inc(v_fst_6248_);
v_snd_6249_ = lean_ctor_get(v_a_6247_, 1);
lean_inc_n(v_snd_6249_, 2);
lean_dec(v_a_6247_);
lean_inc(v___x_6227_);
v___x_6250_ = l_Lean_Kernel_Environment_checkName(v_snd_6249_, v___x_6227_, v_allowPrimitive_6211_);
if (lean_obj_tag(v___x_6250_) == 0)
{
lean_object* v_a_6251_; lean_object* v___x_6253_; uint8_t v_isShared_6254_; uint8_t v_isSharedCheck_6258_; 
lean_dec(v_snd_6249_);
lean_dec(v_fst_6248_);
lean_del_object(v___x_6243_);
lean_dec(v_numMinors_6238_);
lean_dec(v_numMotives_6237_);
lean_dec(v_numIndices_6236_);
lean_dec(v_numParams_6235_);
lean_dec_ref(v_toConstantVal_6234_);
lean_del_object(v___x_6232_);
lean_dec(v___x_6227_);
lean_dec(v_tail_6219_);
lean_dec(v___x_6212_);
lean_dec_ref(v_a_6210_);
lean_dec_ref(v___x_6209_);
lean_dec(v_snd_6208_);
v_a_6251_ = lean_ctor_get(v___x_6250_, 0);
v_isSharedCheck_6258_ = !lean_is_exclusive(v___x_6250_);
if (v_isSharedCheck_6258_ == 0)
{
v___x_6253_ = v___x_6250_;
v_isShared_6254_ = v_isSharedCheck_6258_;
goto v_resetjp_6252_;
}
else
{
lean_inc(v_a_6251_);
lean_dec(v___x_6250_);
v___x_6253_ = lean_box(0);
v_isShared_6254_ = v_isSharedCheck_6258_;
goto v_resetjp_6252_;
}
v_resetjp_6252_:
{
lean_object* v___x_6256_; 
if (v_isShared_6254_ == 0)
{
v___x_6256_ = v___x_6253_;
goto v_reusejp_6255_;
}
else
{
lean_object* v_reuseFailAlloc_6257_; 
v_reuseFailAlloc_6257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6257_, 0, v_a_6251_);
v___x_6256_ = v_reuseFailAlloc_6257_;
goto v_reusejp_6255_;
}
v_reusejp_6255_:
{
return v___x_6256_;
}
}
}
else
{
lean_object* v_levelParams_6259_; lean_object* v_type_6260_; lean_object* v___x_6262_; uint8_t v_isShared_6263_; uint8_t v_isSharedCheck_6276_; 
lean_dec_ref(v___x_6250_);
v_levelParams_6259_ = lean_ctor_get(v_toConstantVal_6234_, 1);
v_type_6260_ = lean_ctor_get(v_toConstantVal_6234_, 2);
v_isSharedCheck_6276_ = !lean_is_exclusive(v_toConstantVal_6234_);
if (v_isSharedCheck_6276_ == 0)
{
lean_object* v_unused_6277_; 
v_unused_6277_ = lean_ctor_get(v_toConstantVal_6234_, 0);
lean_dec(v_unused_6277_);
v___x_6262_ = v_toConstantVal_6234_;
v_isShared_6263_ = v_isSharedCheck_6276_;
goto v_resetjp_6261_;
}
else
{
lean_inc(v_type_6260_);
lean_inc(v_levelParams_6259_);
lean_dec(v_toConstantVal_6234_);
v___x_6262_ = lean_box(0);
v_isShared_6263_ = v_isSharedCheck_6276_;
goto v_resetjp_6261_;
}
v_resetjp_6261_:
{
lean_object* v___x_6264_; lean_object* v___x_6266_; 
lean_inc(v_snd_6208_);
lean_inc_ref(v_a_6210_);
lean_inc_ref(v___x_6209_);
v___x_6264_ = l_Lean4Lean_ElimNestedInductive_Result_restoreNested(v___x_6209_, v_a_6210_, v_type_6260_, v_snd_6208_);
if (v_isShared_6263_ == 0)
{
lean_ctor_set(v___x_6262_, 2, v___x_6264_);
lean_ctor_set(v___x_6262_, 0, v___x_6227_);
v___x_6266_ = v___x_6262_;
goto v_reusejp_6265_;
}
else
{
lean_object* v_reuseFailAlloc_6275_; 
v_reuseFailAlloc_6275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6275_, 0, v___x_6227_);
lean_ctor_set(v_reuseFailAlloc_6275_, 1, v_levelParams_6259_);
lean_ctor_set(v_reuseFailAlloc_6275_, 2, v___x_6264_);
v___x_6266_ = v_reuseFailAlloc_6275_;
goto v_reusejp_6265_;
}
v_reusejp_6265_:
{
lean_object* v___x_6268_; 
lean_inc(v___x_6212_);
if (v_isShared_6244_ == 0)
{
lean_ctor_set(v___x_6243_, 6, v_fst_6248_);
lean_ctor_set(v___x_6243_, 1, v___x_6212_);
lean_ctor_set(v___x_6243_, 0, v___x_6266_);
v___x_6268_ = v___x_6243_;
goto v_reusejp_6267_;
}
else
{
lean_object* v_reuseFailAlloc_6274_; 
v_reuseFailAlloc_6274_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v_reuseFailAlloc_6274_, 0, v___x_6266_);
lean_ctor_set(v_reuseFailAlloc_6274_, 1, v___x_6212_);
lean_ctor_set(v_reuseFailAlloc_6274_, 2, v_numParams_6235_);
lean_ctor_set(v_reuseFailAlloc_6274_, 3, v_numIndices_6236_);
lean_ctor_set(v_reuseFailAlloc_6274_, 4, v_numMotives_6237_);
lean_ctor_set(v_reuseFailAlloc_6274_, 5, v_numMinors_6238_);
lean_ctor_set(v_reuseFailAlloc_6274_, 6, v_fst_6248_);
lean_ctor_set_uint8(v_reuseFailAlloc_6274_, sizeof(void*)*7, v_k_6240_);
lean_ctor_set_uint8(v_reuseFailAlloc_6274_, sizeof(void*)*7 + 1, v_isUnsafe_6241_);
v___x_6268_ = v_reuseFailAlloc_6274_;
goto v_reusejp_6267_;
}
v_reusejp_6267_:
{
lean_object* v___x_6270_; 
if (v_isShared_6233_ == 0)
{
lean_ctor_set(v___x_6232_, 0, v___x_6268_);
v___x_6270_ = v___x_6232_;
goto v_reusejp_6269_;
}
else
{
lean_object* v_reuseFailAlloc_6273_; 
v_reuseFailAlloc_6273_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6273_, 0, v___x_6268_);
v___x_6270_ = v_reuseFailAlloc_6273_;
goto v_reusejp_6269_;
}
v_reusejp_6269_:
{
lean_object* v___x_6271_; lean_object* v___x_6272_; 
v___x_6271_ = lean_environment_add(v_snd_6249_, v___x_6270_);
v___x_6272_ = l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7(v_snd_6208_, v_a_6210_, v___x_6209_, v_allowPrimitive_6211_, v___x_6212_, v_tail_6219_, v___x_6271_);
return v___x_6272_;
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
lean_dec(v_val_6229_);
lean_dec(v___x_6227_);
lean_dec(v_head_6218_);
v___y_6221_ = v___y_6214_;
goto v___jp_6220_;
}
}
else
{
lean_dec(v___x_6228_);
lean_dec(v___x_6227_);
lean_dec(v_head_6218_);
v___y_6221_ = v___y_6214_;
goto v___jp_6220_;
}
v___jp_6220_:
{
lean_object* v___x_6222_; lean_object* v___x_6223_; 
v___x_6222_ = lean_obj_once(&l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1, &l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1_once, _init_l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1);
v___x_6223_ = l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(v___x_6222_, v___y_6221_);
if (lean_obj_tag(v___x_6223_) == 0)
{
lean_dec(v_tail_6219_);
lean_dec(v___x_6212_);
lean_dec_ref(v_a_6210_);
lean_dec_ref(v___x_6209_);
lean_dec(v_snd_6208_);
return v___x_6223_;
}
else
{
lean_object* v_a_6224_; lean_object* v_snd_6225_; lean_object* v___x_6226_; 
v_a_6224_ = lean_ctor_get(v___x_6223_, 0);
lean_inc(v_a_6224_);
lean_dec_ref(v___x_6223_);
v_snd_6225_ = lean_ctor_get(v_a_6224_, 1);
lean_inc(v_snd_6225_);
lean_dec(v_a_6224_);
v___x_6226_ = l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7(v_snd_6208_, v_a_6210_, v___x_6209_, v_allowPrimitive_6211_, v___x_6212_, v_tail_6219_, v_snd_6225_);
return v___x_6226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean4Lean_Environment_addInductive_spec__6___boxed(lean_object* v_snd_6281_, lean_object* v___x_6282_, lean_object* v_a_6283_, lean_object* v_allowPrimitive_6284_, lean_object* v___x_6285_, lean_object* v_as_6286_, lean_object* v___y_6287_){
_start:
{
uint8_t v_allowPrimitive_boxed_6288_; lean_object* v_res_6289_; 
v_allowPrimitive_boxed_6288_ = lean_unbox(v_allowPrimitive_6284_);
v_res_6289_ = l_List_forM___at___00Lean4Lean_Environment_addInductive_spec__6(v_snd_6281_, v___x_6282_, v_a_6283_, v_allowPrimitive_boxed_6288_, v___x_6285_, v_as_6286_, v___y_6287_);
return v_res_6289_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; 
v___x_6290_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_6291_ = lean_unsigned_to_nat(57u);
v___x_6292_ = lean_unsigned_to_nat(751u);
v___x_6293_ = ((lean_object*)(l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__0));
v___x_6294_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_6295_ = l_mkPanicMessageWithDecl(v___x_6294_, v___x_6293_, v___x_6292_, v___x_6291_, v___x_6290_);
return v___x_6295_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg(lean_object* v_a_6296_, uint8_t v_allowPrimitive_6297_, lean_object* v___x_6298_, lean_object* v_as_x27_6299_, lean_object* v_b_6300_, lean_object* v___y_6301_){
_start:
{
if (lean_obj_tag(v_as_x27_6299_) == 0)
{
lean_object* v___x_6302_; lean_object* v___x_6303_; 
lean_dec_ref(v___x_6298_);
lean_dec_ref(v_a_6296_);
v___x_6302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6302_, 0, v_b_6300_);
lean_ctor_set(v___x_6302_, 1, v___y_6301_);
v___x_6303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6303_, 0, v___x_6302_);
return v___x_6303_;
}
else
{
lean_object* v_head_6304_; lean_object* v_tail_6305_; lean_object* v___x_6306_; lean_object* v___y_6308_; lean_object* v___x_6314_; 
v_head_6304_ = lean_ctor_get(v_as_x27_6299_, 0);
v_tail_6305_ = lean_ctor_get(v_as_x27_6299_, 1);
v___x_6306_ = lean_box(0);
lean_inc(v_head_6304_);
lean_inc_ref(v_a_6296_);
v___x_6314_ = lean_environment_find(v_a_6296_, v_head_6304_);
if (lean_obj_tag(v___x_6314_) == 1)
{
lean_object* v_val_6315_; 
v_val_6315_ = lean_ctor_get(v___x_6314_, 0);
lean_inc(v_val_6315_);
lean_dec_ref(v___x_6314_);
if (lean_obj_tag(v_val_6315_) == 6)
{
lean_object* v_val_6316_; lean_object* v___x_6318_; uint8_t v_isShared_6319_; uint8_t v_isSharedCheck_6359_; 
v_val_6316_ = lean_ctor_get(v_val_6315_, 0);
v_isSharedCheck_6359_ = !lean_is_exclusive(v_val_6315_);
if (v_isSharedCheck_6359_ == 0)
{
v___x_6318_ = v_val_6315_;
v_isShared_6319_ = v_isSharedCheck_6359_;
goto v_resetjp_6317_;
}
else
{
lean_inc(v_val_6316_);
lean_dec(v_val_6315_);
v___x_6318_ = lean_box(0);
v_isShared_6319_ = v_isSharedCheck_6359_;
goto v_resetjp_6317_;
}
v_resetjp_6317_:
{
lean_object* v_toConstantVal_6320_; lean_object* v_induct_6321_; lean_object* v_cidx_6322_; lean_object* v_numParams_6323_; lean_object* v_numFields_6324_; uint8_t v_isUnsafe_6325_; lean_object* v___x_6327_; uint8_t v_isShared_6328_; uint8_t v_isSharedCheck_6358_; 
v_toConstantVal_6320_ = lean_ctor_get(v_val_6316_, 0);
v_induct_6321_ = lean_ctor_get(v_val_6316_, 1);
v_cidx_6322_ = lean_ctor_get(v_val_6316_, 2);
v_numParams_6323_ = lean_ctor_get(v_val_6316_, 3);
v_numFields_6324_ = lean_ctor_get(v_val_6316_, 4);
v_isUnsafe_6325_ = lean_ctor_get_uint8(v_val_6316_, sizeof(void*)*5);
v_isSharedCheck_6358_ = !lean_is_exclusive(v_val_6316_);
if (v_isSharedCheck_6358_ == 0)
{
v___x_6327_ = v_val_6316_;
v_isShared_6328_ = v_isSharedCheck_6358_;
goto v_resetjp_6326_;
}
else
{
lean_inc(v_numFields_6324_);
lean_inc(v_numParams_6323_);
lean_inc(v_cidx_6322_);
lean_inc(v_induct_6321_);
lean_inc(v_toConstantVal_6320_);
lean_dec(v_val_6316_);
v___x_6327_ = lean_box(0);
v_isShared_6328_ = v_isSharedCheck_6358_;
goto v_resetjp_6326_;
}
v_resetjp_6326_:
{
lean_object* v_name_6329_; lean_object* v_levelParams_6330_; lean_object* v_type_6331_; lean_object* v___x_6333_; uint8_t v_isShared_6334_; uint8_t v_isSharedCheck_6357_; 
v_name_6329_ = lean_ctor_get(v_toConstantVal_6320_, 0);
v_levelParams_6330_ = lean_ctor_get(v_toConstantVal_6320_, 1);
v_type_6331_ = lean_ctor_get(v_toConstantVal_6320_, 2);
v_isSharedCheck_6357_ = !lean_is_exclusive(v_toConstantVal_6320_);
if (v_isSharedCheck_6357_ == 0)
{
v___x_6333_ = v_toConstantVal_6320_;
v_isShared_6334_ = v_isSharedCheck_6357_;
goto v_resetjp_6332_;
}
else
{
lean_inc(v_type_6331_);
lean_inc(v_levelParams_6330_);
lean_inc(v_name_6329_);
lean_dec(v_toConstantVal_6320_);
v___x_6333_ = lean_box(0);
v_isShared_6334_ = v_isSharedCheck_6357_;
goto v_resetjp_6332_;
}
v_resetjp_6332_:
{
lean_object* v___x_6335_; 
lean_inc(v_name_6329_);
lean_inc_ref(v___y_6301_);
v___x_6335_ = l_Lean_Kernel_Environment_checkName(v___y_6301_, v_name_6329_, v_allowPrimitive_6297_);
if (lean_obj_tag(v___x_6335_) == 0)
{
lean_object* v_a_6336_; lean_object* v___x_6338_; uint8_t v_isShared_6339_; uint8_t v_isSharedCheck_6343_; 
lean_del_object(v___x_6333_);
lean_dec_ref(v_type_6331_);
lean_dec(v_levelParams_6330_);
lean_dec(v_name_6329_);
lean_del_object(v___x_6327_);
lean_dec(v_numFields_6324_);
lean_dec(v_numParams_6323_);
lean_dec(v_cidx_6322_);
lean_dec(v_induct_6321_);
lean_del_object(v___x_6318_);
lean_dec_ref(v___y_6301_);
lean_dec_ref(v___x_6298_);
lean_dec_ref(v_a_6296_);
v_a_6336_ = lean_ctor_get(v___x_6335_, 0);
v_isSharedCheck_6343_ = !lean_is_exclusive(v___x_6335_);
if (v_isSharedCheck_6343_ == 0)
{
v___x_6338_ = v___x_6335_;
v_isShared_6339_ = v_isSharedCheck_6343_;
goto v_resetjp_6337_;
}
else
{
lean_inc(v_a_6336_);
lean_dec(v___x_6335_);
v___x_6338_ = lean_box(0);
v_isShared_6339_ = v_isSharedCheck_6343_;
goto v_resetjp_6337_;
}
v_resetjp_6337_:
{
lean_object* v___x_6341_; 
if (v_isShared_6339_ == 0)
{
v___x_6341_ = v___x_6338_;
goto v_reusejp_6340_;
}
else
{
lean_object* v_reuseFailAlloc_6342_; 
v_reuseFailAlloc_6342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6342_, 0, v_a_6336_);
v___x_6341_ = v_reuseFailAlloc_6342_;
goto v_reusejp_6340_;
}
v_reusejp_6340_:
{
return v___x_6341_;
}
}
}
else
{
lean_object* v___x_6344_; lean_object* v___x_6345_; lean_object* v___x_6347_; 
lean_dec_ref(v___x_6335_);
v___x_6344_ = lean_box(1);
lean_inc_ref(v_a_6296_);
lean_inc_ref(v___x_6298_);
v___x_6345_ = l_Lean4Lean_ElimNestedInductive_Result_restoreNested(v___x_6298_, v_a_6296_, v_type_6331_, v___x_6344_);
if (v_isShared_6334_ == 0)
{
lean_ctor_set(v___x_6333_, 2, v___x_6345_);
v___x_6347_ = v___x_6333_;
goto v_reusejp_6346_;
}
else
{
lean_object* v_reuseFailAlloc_6356_; 
v_reuseFailAlloc_6356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6356_, 0, v_name_6329_);
lean_ctor_set(v_reuseFailAlloc_6356_, 1, v_levelParams_6330_);
lean_ctor_set(v_reuseFailAlloc_6356_, 2, v___x_6345_);
v___x_6347_ = v_reuseFailAlloc_6356_;
goto v_reusejp_6346_;
}
v_reusejp_6346_:
{
lean_object* v___x_6349_; 
if (v_isShared_6328_ == 0)
{
lean_ctor_set(v___x_6327_, 0, v___x_6347_);
v___x_6349_ = v___x_6327_;
goto v_reusejp_6348_;
}
else
{
lean_object* v_reuseFailAlloc_6355_; 
v_reuseFailAlloc_6355_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v_reuseFailAlloc_6355_, 0, v___x_6347_);
lean_ctor_set(v_reuseFailAlloc_6355_, 1, v_induct_6321_);
lean_ctor_set(v_reuseFailAlloc_6355_, 2, v_cidx_6322_);
lean_ctor_set(v_reuseFailAlloc_6355_, 3, v_numParams_6323_);
lean_ctor_set(v_reuseFailAlloc_6355_, 4, v_numFields_6324_);
lean_ctor_set_uint8(v_reuseFailAlloc_6355_, sizeof(void*)*5, v_isUnsafe_6325_);
v___x_6349_ = v_reuseFailAlloc_6355_;
goto v_reusejp_6348_;
}
v_reusejp_6348_:
{
lean_object* v___x_6351_; 
if (v_isShared_6319_ == 0)
{
lean_ctor_set(v___x_6318_, 0, v___x_6349_);
v___x_6351_ = v___x_6318_;
goto v_reusejp_6350_;
}
else
{
lean_object* v_reuseFailAlloc_6354_; 
v_reuseFailAlloc_6354_ = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6354_, 0, v___x_6349_);
v___x_6351_ = v_reuseFailAlloc_6354_;
goto v_reusejp_6350_;
}
v_reusejp_6350_:
{
lean_object* v___x_6352_; 
v___x_6352_ = lean_environment_add(v___y_6301_, v___x_6351_);
v_as_x27_6299_ = v_tail_6305_;
v_b_6300_ = v___x_6306_;
v___y_6301_ = v___x_6352_;
goto _start;
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
lean_dec(v_val_6315_);
v___y_6308_ = v___y_6301_;
goto v___jp_6307_;
}
}
else
{
lean_dec(v___x_6314_);
v___y_6308_ = v___y_6301_;
goto v___jp_6307_;
}
v___jp_6307_:
{
lean_object* v___x_6309_; lean_object* v___x_6310_; 
v___x_6309_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___closed__0, &l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___closed__0);
v___x_6310_ = l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(v___x_6309_, v___y_6308_);
if (lean_obj_tag(v___x_6310_) == 0)
{
lean_dec_ref(v___x_6298_);
lean_dec_ref(v_a_6296_);
return v___x_6310_;
}
else
{
lean_object* v_a_6311_; lean_object* v_snd_6312_; 
v_a_6311_ = lean_ctor_get(v___x_6310_, 0);
lean_inc(v_a_6311_);
lean_dec_ref(v___x_6310_);
v_snd_6312_ = lean_ctor_get(v_a_6311_, 1);
lean_inc(v_snd_6312_);
lean_dec(v_a_6311_);
v_as_x27_6299_ = v_tail_6305_;
v_b_6300_ = v___x_6306_;
v___y_6301_ = v_snd_6312_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg___boxed(lean_object* v_a_6360_, lean_object* v_allowPrimitive_6361_, lean_object* v___x_6362_, lean_object* v_as_x27_6363_, lean_object* v_b_6364_, lean_object* v___y_6365_){
_start:
{
uint8_t v_allowPrimitive_boxed_6366_; lean_object* v_res_6367_; 
v_allowPrimitive_boxed_6366_ = lean_unbox(v_allowPrimitive_6361_);
v_res_6367_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg(v_a_6360_, v_allowPrimitive_boxed_6366_, v___x_6362_, v_as_x27_6363_, v_b_6364_, v___y_6365_);
lean_dec(v_as_x27_6363_);
return v_res_6367_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_6368_; lean_object* v___x_6369_; lean_object* v___x_6370_; lean_object* v___x_6371_; lean_object* v___x_6372_; lean_object* v___x_6373_; 
v___x_6368_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreCtorName___closed__1));
v___x_6369_ = lean_unsigned_to_nat(60u);
v___x_6370_ = lean_unsigned_to_nat(747u);
v___x_6371_ = ((lean_object*)(l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__0));
v___x_6372_ = ((lean_object*)(l_Lean4Lean_AddInductive_checkInductiveTypes_loopInd___redArg___closed__0));
v___x_6373_ = l_mkPanicMessageWithDecl(v___x_6372_, v___x_6371_, v___x_6370_, v___x_6369_, v___x_6368_);
return v___x_6373_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg(lean_object* v_a_6374_, uint8_t v_allowPrimitive_6375_, lean_object* v___x_6376_, lean_object* v___x_6377_, lean_object* v_snd_6378_, lean_object* v_as_x27_6379_, lean_object* v_b_6380_, lean_object* v___y_6381_){
_start:
{
if (lean_obj_tag(v_as_x27_6379_) == 0)
{
lean_object* v___x_6382_; lean_object* v___x_6383_; 
lean_dec(v_snd_6378_);
lean_dec_ref(v___x_6377_);
lean_dec(v___x_6376_);
lean_dec_ref(v_a_6374_);
v___x_6382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6382_, 0, v_b_6380_);
lean_ctor_set(v___x_6382_, 1, v___y_6381_);
v___x_6383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6383_, 0, v___x_6382_);
return v___x_6383_;
}
else
{
lean_object* v_head_6384_; lean_object* v_tail_6385_; lean_object* v_name_6386_; lean_object* v___x_6387_; lean_object* v___y_6389_; lean_object* v___x_6395_; 
v_head_6384_ = lean_ctor_get(v_as_x27_6379_, 0);
v_tail_6385_ = lean_ctor_get(v_as_x27_6379_, 1);
v_name_6386_ = lean_ctor_get(v_head_6384_, 0);
v___x_6387_ = lean_box(0);
lean_inc(v_name_6386_);
lean_inc_ref(v_a_6374_);
v___x_6395_ = lean_environment_find(v_a_6374_, v_name_6386_);
if (lean_obj_tag(v___x_6395_) == 1)
{
lean_object* v_val_6396_; 
v_val_6396_ = lean_ctor_get(v___x_6395_, 0);
lean_inc(v_val_6396_);
lean_dec_ref(v___x_6395_);
if (lean_obj_tag(v_val_6396_) == 5)
{
lean_object* v_val_6397_; lean_object* v___x_6399_; uint8_t v_isShared_6400_; uint8_t v_isSharedCheck_6495_; 
v_val_6397_ = lean_ctor_get(v_val_6396_, 0);
v_isSharedCheck_6495_ = !lean_is_exclusive(v_val_6396_);
if (v_isSharedCheck_6495_ == 0)
{
v___x_6399_ = v_val_6396_;
v_isShared_6400_ = v_isSharedCheck_6495_;
goto v_resetjp_6398_;
}
else
{
lean_inc(v_val_6397_);
lean_dec(v_val_6396_);
v___x_6399_ = lean_box(0);
v_isShared_6400_ = v_isSharedCheck_6495_;
goto v_resetjp_6398_;
}
v_resetjp_6398_:
{
lean_object* v_toConstantVal_6401_; lean_object* v_numParams_6402_; lean_object* v_numIndices_6403_; lean_object* v_ctors_6404_; lean_object* v_numNested_6405_; uint8_t v_isRec_6406_; uint8_t v_isUnsafe_6407_; uint8_t v_isReflexive_6408_; lean_object* v___x_6410_; uint8_t v_isShared_6411_; uint8_t v_isSharedCheck_6493_; 
v_toConstantVal_6401_ = lean_ctor_get(v_val_6397_, 0);
v_numParams_6402_ = lean_ctor_get(v_val_6397_, 1);
v_numIndices_6403_ = lean_ctor_get(v_val_6397_, 2);
v_ctors_6404_ = lean_ctor_get(v_val_6397_, 4);
v_numNested_6405_ = lean_ctor_get(v_val_6397_, 5);
v_isRec_6406_ = lean_ctor_get_uint8(v_val_6397_, sizeof(void*)*6);
v_isUnsafe_6407_ = lean_ctor_get_uint8(v_val_6397_, sizeof(void*)*6 + 1);
v_isReflexive_6408_ = lean_ctor_get_uint8(v_val_6397_, sizeof(void*)*6 + 2);
v_isSharedCheck_6493_ = !lean_is_exclusive(v_val_6397_);
if (v_isSharedCheck_6493_ == 0)
{
lean_object* v_unused_6494_; 
v_unused_6494_ = lean_ctor_get(v_val_6397_, 3);
lean_dec(v_unused_6494_);
v___x_6410_ = v_val_6397_;
v_isShared_6411_ = v_isSharedCheck_6493_;
goto v_resetjp_6409_;
}
else
{
lean_inc(v_numNested_6405_);
lean_inc(v_ctors_6404_);
lean_inc(v_numIndices_6403_);
lean_inc(v_numParams_6402_);
lean_inc(v_toConstantVal_6401_);
lean_dec(v_val_6397_);
v___x_6410_ = lean_box(0);
v_isShared_6411_ = v_isSharedCheck_6493_;
goto v_resetjp_6409_;
}
v_resetjp_6409_:
{
lean_object* v_name_6412_; lean_object* v___x_6413_; 
v_name_6412_ = lean_ctor_get(v_toConstantVal_6401_, 0);
lean_inc(v_name_6412_);
lean_inc_ref(v___y_6381_);
v___x_6413_ = l_Lean_Kernel_Environment_checkName(v___y_6381_, v_name_6412_, v_allowPrimitive_6375_);
if (lean_obj_tag(v___x_6413_) == 0)
{
lean_object* v_a_6414_; lean_object* v___x_6416_; uint8_t v_isShared_6417_; uint8_t v_isSharedCheck_6421_; 
lean_del_object(v___x_6410_);
lean_dec(v_numNested_6405_);
lean_dec(v_ctors_6404_);
lean_dec(v_numIndices_6403_);
lean_dec(v_numParams_6402_);
lean_dec_ref(v_toConstantVal_6401_);
lean_del_object(v___x_6399_);
lean_dec_ref(v___y_6381_);
lean_dec(v_snd_6378_);
lean_dec_ref(v___x_6377_);
lean_dec(v___x_6376_);
lean_dec_ref(v_a_6374_);
v_a_6414_ = lean_ctor_get(v___x_6413_, 0);
v_isSharedCheck_6421_ = !lean_is_exclusive(v___x_6413_);
if (v_isSharedCheck_6421_ == 0)
{
v___x_6416_ = v___x_6413_;
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
else
{
lean_inc(v_a_6414_);
lean_dec(v___x_6413_);
v___x_6416_ = lean_box(0);
v_isShared_6417_ = v_isSharedCheck_6421_;
goto v_resetjp_6415_;
}
v_resetjp_6415_:
{
lean_object* v___x_6419_; 
if (v_isShared_6417_ == 0)
{
v___x_6419_ = v___x_6416_;
goto v_reusejp_6418_;
}
else
{
lean_object* v_reuseFailAlloc_6420_; 
v_reuseFailAlloc_6420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6420_, 0, v_a_6414_);
v___x_6419_ = v_reuseFailAlloc_6420_;
goto v_reusejp_6418_;
}
v_reusejp_6418_:
{
return v___x_6419_;
}
}
}
else
{
lean_object* v___x_6423_; 
lean_dec_ref(v___x_6413_);
lean_inc(v_ctors_6404_);
lean_inc(v___x_6376_);
if (v_isShared_6411_ == 0)
{
lean_ctor_set(v___x_6410_, 3, v___x_6376_);
v___x_6423_ = v___x_6410_;
goto v_reusejp_6422_;
}
else
{
lean_object* v_reuseFailAlloc_6492_; 
v_reuseFailAlloc_6492_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_6492_, 0, v_toConstantVal_6401_);
lean_ctor_set(v_reuseFailAlloc_6492_, 1, v_numParams_6402_);
lean_ctor_set(v_reuseFailAlloc_6492_, 2, v_numIndices_6403_);
lean_ctor_set(v_reuseFailAlloc_6492_, 3, v___x_6376_);
lean_ctor_set(v_reuseFailAlloc_6492_, 4, v_ctors_6404_);
lean_ctor_set(v_reuseFailAlloc_6492_, 5, v_numNested_6405_);
lean_ctor_set_uint8(v_reuseFailAlloc_6492_, sizeof(void*)*6, v_isRec_6406_);
lean_ctor_set_uint8(v_reuseFailAlloc_6492_, sizeof(void*)*6 + 1, v_isUnsafe_6407_);
lean_ctor_set_uint8(v_reuseFailAlloc_6492_, sizeof(void*)*6 + 2, v_isReflexive_6408_);
v___x_6423_ = v_reuseFailAlloc_6492_;
goto v_reusejp_6422_;
}
v_reusejp_6422_:
{
lean_object* v___x_6425_; 
if (v_isShared_6400_ == 0)
{
lean_ctor_set(v___x_6399_, 0, v___x_6423_);
v___x_6425_ = v___x_6399_;
goto v_reusejp_6424_;
}
else
{
lean_object* v_reuseFailAlloc_6491_; 
v_reuseFailAlloc_6491_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6491_, 0, v___x_6423_);
v___x_6425_ = v_reuseFailAlloc_6491_;
goto v_reusejp_6424_;
}
v_reusejp_6424_:
{
lean_object* v___x_6426_; lean_object* v___x_6427_; 
v___x_6426_ = lean_environment_add(v___y_6381_, v___x_6425_);
lean_inc_ref(v___x_6377_);
lean_inc_ref(v_a_6374_);
v___x_6427_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg(v_a_6374_, v_allowPrimitive_6375_, v___x_6377_, v_ctors_6404_, v___x_6387_, v___x_6426_);
lean_dec(v_ctors_6404_);
if (lean_obj_tag(v___x_6427_) == 0)
{
lean_dec(v_snd_6378_);
lean_dec_ref(v___x_6377_);
lean_dec(v___x_6376_);
lean_dec_ref(v_a_6374_);
return v___x_6427_;
}
else
{
lean_object* v_a_6428_; lean_object* v_snd_6429_; lean_object* v___x_6436_; lean_object* v___x_6437_; lean_object* v___x_6438_; 
v_a_6428_ = lean_ctor_get(v___x_6427_, 0);
lean_inc(v_a_6428_);
lean_dec_ref(v___x_6427_);
v_snd_6429_ = lean_ctor_get(v_a_6428_, 1);
lean_inc(v_snd_6429_);
lean_dec(v_a_6428_);
lean_inc(v_name_6386_);
v___x_6436_ = l_Lean_mkRecName(v_name_6386_);
v___x_6437_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(v_snd_6378_, v___x_6436_, v___x_6436_);
lean_inc(v___x_6436_);
lean_inc_ref(v_a_6374_);
v___x_6438_ = lean_environment_find(v_a_6374_, v___x_6436_);
if (lean_obj_tag(v___x_6438_) == 1)
{
lean_object* v_val_6439_; 
v_val_6439_ = lean_ctor_get(v___x_6438_, 0);
lean_inc(v_val_6439_);
lean_dec_ref(v___x_6438_);
if (lean_obj_tag(v_val_6439_) == 7)
{
lean_object* v_val_6440_; lean_object* v___x_6442_; uint8_t v_isShared_6443_; uint8_t v_isSharedCheck_6490_; 
v_val_6440_ = lean_ctor_get(v_val_6439_, 0);
v_isSharedCheck_6490_ = !lean_is_exclusive(v_val_6439_);
if (v_isSharedCheck_6490_ == 0)
{
v___x_6442_ = v_val_6439_;
v_isShared_6443_ = v_isSharedCheck_6490_;
goto v_resetjp_6441_;
}
else
{
lean_inc(v_val_6440_);
lean_dec(v_val_6439_);
v___x_6442_ = lean_box(0);
v_isShared_6443_ = v_isSharedCheck_6490_;
goto v_resetjp_6441_;
}
v_resetjp_6441_:
{
lean_object* v_toConstantVal_6444_; lean_object* v_numParams_6445_; lean_object* v_numIndices_6446_; lean_object* v_numMotives_6447_; lean_object* v_numMinors_6448_; lean_object* v_rules_6449_; uint8_t v_k_6450_; uint8_t v_isUnsafe_6451_; lean_object* v___x_6453_; uint8_t v_isShared_6454_; uint8_t v_isSharedCheck_6488_; 
v_toConstantVal_6444_ = lean_ctor_get(v_val_6440_, 0);
v_numParams_6445_ = lean_ctor_get(v_val_6440_, 2);
v_numIndices_6446_ = lean_ctor_get(v_val_6440_, 3);
v_numMotives_6447_ = lean_ctor_get(v_val_6440_, 4);
v_numMinors_6448_ = lean_ctor_get(v_val_6440_, 5);
v_rules_6449_ = lean_ctor_get(v_val_6440_, 6);
v_k_6450_ = lean_ctor_get_uint8(v_val_6440_, sizeof(void*)*7);
v_isUnsafe_6451_ = lean_ctor_get_uint8(v_val_6440_, sizeof(void*)*7 + 1);
v_isSharedCheck_6488_ = !lean_is_exclusive(v_val_6440_);
if (v_isSharedCheck_6488_ == 0)
{
lean_object* v_unused_6489_; 
v_unused_6489_ = lean_ctor_get(v_val_6440_, 1);
lean_dec(v_unused_6489_);
v___x_6453_ = v_val_6440_;
v_isShared_6454_ = v_isSharedCheck_6488_;
goto v_resetjp_6452_;
}
else
{
lean_inc(v_rules_6449_);
lean_inc(v_numMinors_6448_);
lean_inc(v_numMotives_6447_);
lean_inc(v_numIndices_6446_);
lean_inc(v_numParams_6445_);
lean_inc(v_toConstantVal_6444_);
lean_dec(v_val_6440_);
v___x_6453_ = lean_box(0);
v_isShared_6454_ = v_isSharedCheck_6488_;
goto v_resetjp_6452_;
}
v_resetjp_6452_:
{
lean_object* v___x_6455_; lean_object* v___x_6456_; lean_object* v_a_6457_; lean_object* v_fst_6458_; lean_object* v_snd_6459_; lean_object* v___x_6460_; 
v___x_6455_ = lean_box(0);
lean_inc(v_snd_6378_);
lean_inc_ref(v_a_6374_);
lean_inc_ref(v___x_6377_);
v___x_6456_ = l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3(v___x_6377_, v_a_6374_, v_snd_6378_, v___x_6437_, v___x_6436_, v_rules_6449_, v___x_6455_, v_snd_6429_);
lean_dec(v___x_6436_);
v_a_6457_ = lean_ctor_get(v___x_6456_, 0);
lean_inc(v_a_6457_);
lean_dec_ref(v___x_6456_);
v_fst_6458_ = lean_ctor_get(v_a_6457_, 0);
lean_inc(v_fst_6458_);
v_snd_6459_ = lean_ctor_get(v_a_6457_, 1);
lean_inc_n(v_snd_6459_, 2);
lean_dec(v_a_6457_);
lean_inc(v___x_6437_);
v___x_6460_ = l_Lean_Kernel_Environment_checkName(v_snd_6459_, v___x_6437_, v_allowPrimitive_6375_);
if (lean_obj_tag(v___x_6460_) == 0)
{
lean_object* v_a_6461_; lean_object* v___x_6463_; uint8_t v_isShared_6464_; uint8_t v_isSharedCheck_6468_; 
lean_dec(v_snd_6459_);
lean_dec(v_fst_6458_);
lean_del_object(v___x_6453_);
lean_dec(v_numMinors_6448_);
lean_dec(v_numMotives_6447_);
lean_dec(v_numIndices_6446_);
lean_dec(v_numParams_6445_);
lean_dec_ref(v_toConstantVal_6444_);
lean_del_object(v___x_6442_);
lean_dec(v___x_6437_);
lean_dec(v_snd_6378_);
lean_dec_ref(v___x_6377_);
lean_dec(v___x_6376_);
lean_dec_ref(v_a_6374_);
v_a_6461_ = lean_ctor_get(v___x_6460_, 0);
v_isSharedCheck_6468_ = !lean_is_exclusive(v___x_6460_);
if (v_isSharedCheck_6468_ == 0)
{
v___x_6463_ = v___x_6460_;
v_isShared_6464_ = v_isSharedCheck_6468_;
goto v_resetjp_6462_;
}
else
{
lean_inc(v_a_6461_);
lean_dec(v___x_6460_);
v___x_6463_ = lean_box(0);
v_isShared_6464_ = v_isSharedCheck_6468_;
goto v_resetjp_6462_;
}
v_resetjp_6462_:
{
lean_object* v___x_6466_; 
if (v_isShared_6464_ == 0)
{
v___x_6466_ = v___x_6463_;
goto v_reusejp_6465_;
}
else
{
lean_object* v_reuseFailAlloc_6467_; 
v_reuseFailAlloc_6467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6467_, 0, v_a_6461_);
v___x_6466_ = v_reuseFailAlloc_6467_;
goto v_reusejp_6465_;
}
v_reusejp_6465_:
{
return v___x_6466_;
}
}
}
else
{
lean_object* v_levelParams_6469_; lean_object* v_type_6470_; lean_object* v___x_6472_; uint8_t v_isShared_6473_; uint8_t v_isSharedCheck_6486_; 
lean_dec_ref(v___x_6460_);
v_levelParams_6469_ = lean_ctor_get(v_toConstantVal_6444_, 1);
v_type_6470_ = lean_ctor_get(v_toConstantVal_6444_, 2);
v_isSharedCheck_6486_ = !lean_is_exclusive(v_toConstantVal_6444_);
if (v_isSharedCheck_6486_ == 0)
{
lean_object* v_unused_6487_; 
v_unused_6487_ = lean_ctor_get(v_toConstantVal_6444_, 0);
lean_dec(v_unused_6487_);
v___x_6472_ = v_toConstantVal_6444_;
v_isShared_6473_ = v_isSharedCheck_6486_;
goto v_resetjp_6471_;
}
else
{
lean_inc(v_type_6470_);
lean_inc(v_levelParams_6469_);
lean_dec(v_toConstantVal_6444_);
v___x_6472_ = lean_box(0);
v_isShared_6473_ = v_isSharedCheck_6486_;
goto v_resetjp_6471_;
}
v_resetjp_6471_:
{
lean_object* v___x_6474_; lean_object* v___x_6476_; 
lean_inc(v_snd_6378_);
lean_inc_ref(v_a_6374_);
lean_inc_ref(v___x_6377_);
v___x_6474_ = l_Lean4Lean_ElimNestedInductive_Result_restoreNested(v___x_6377_, v_a_6374_, v_type_6470_, v_snd_6378_);
if (v_isShared_6473_ == 0)
{
lean_ctor_set(v___x_6472_, 2, v___x_6474_);
lean_ctor_set(v___x_6472_, 0, v___x_6437_);
v___x_6476_ = v___x_6472_;
goto v_reusejp_6475_;
}
else
{
lean_object* v_reuseFailAlloc_6485_; 
v_reuseFailAlloc_6485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6485_, 0, v___x_6437_);
lean_ctor_set(v_reuseFailAlloc_6485_, 1, v_levelParams_6469_);
lean_ctor_set(v_reuseFailAlloc_6485_, 2, v___x_6474_);
v___x_6476_ = v_reuseFailAlloc_6485_;
goto v_reusejp_6475_;
}
v_reusejp_6475_:
{
lean_object* v___x_6478_; 
lean_inc(v___x_6376_);
if (v_isShared_6454_ == 0)
{
lean_ctor_set(v___x_6453_, 6, v_fst_6458_);
lean_ctor_set(v___x_6453_, 1, v___x_6376_);
lean_ctor_set(v___x_6453_, 0, v___x_6476_);
v___x_6478_ = v___x_6453_;
goto v_reusejp_6477_;
}
else
{
lean_object* v_reuseFailAlloc_6484_; 
v_reuseFailAlloc_6484_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v_reuseFailAlloc_6484_, 0, v___x_6476_);
lean_ctor_set(v_reuseFailAlloc_6484_, 1, v___x_6376_);
lean_ctor_set(v_reuseFailAlloc_6484_, 2, v_numParams_6445_);
lean_ctor_set(v_reuseFailAlloc_6484_, 3, v_numIndices_6446_);
lean_ctor_set(v_reuseFailAlloc_6484_, 4, v_numMotives_6447_);
lean_ctor_set(v_reuseFailAlloc_6484_, 5, v_numMinors_6448_);
lean_ctor_set(v_reuseFailAlloc_6484_, 6, v_fst_6458_);
lean_ctor_set_uint8(v_reuseFailAlloc_6484_, sizeof(void*)*7, v_k_6450_);
lean_ctor_set_uint8(v_reuseFailAlloc_6484_, sizeof(void*)*7 + 1, v_isUnsafe_6451_);
v___x_6478_ = v_reuseFailAlloc_6484_;
goto v_reusejp_6477_;
}
v_reusejp_6477_:
{
lean_object* v___x_6480_; 
if (v_isShared_6443_ == 0)
{
lean_ctor_set(v___x_6442_, 0, v___x_6478_);
v___x_6480_ = v___x_6442_;
goto v_reusejp_6479_;
}
else
{
lean_object* v_reuseFailAlloc_6483_; 
v_reuseFailAlloc_6483_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6483_, 0, v___x_6478_);
v___x_6480_ = v_reuseFailAlloc_6483_;
goto v_reusejp_6479_;
}
v_reusejp_6479_:
{
lean_object* v___x_6481_; 
v___x_6481_ = lean_environment_add(v_snd_6459_, v___x_6480_);
v_as_x27_6379_ = v_tail_6385_;
v_b_6380_ = v___x_6387_;
v___y_6381_ = v___x_6481_;
goto _start;
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
lean_dec(v_val_6439_);
lean_dec(v___x_6437_);
lean_dec(v___x_6436_);
goto v___jp_6430_;
}
}
else
{
lean_dec(v___x_6438_);
lean_dec(v___x_6437_);
lean_dec(v___x_6436_);
goto v___jp_6430_;
}
v___jp_6430_:
{
lean_object* v___x_6431_; lean_object* v___x_6432_; 
v___x_6431_ = lean_obj_once(&l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1, &l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1_once, _init_l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1);
v___x_6432_ = l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(v___x_6431_, v_snd_6429_);
if (lean_obj_tag(v___x_6432_) == 0)
{
lean_dec(v_snd_6378_);
lean_dec_ref(v___x_6377_);
lean_dec(v___x_6376_);
lean_dec_ref(v_a_6374_);
return v___x_6432_;
}
else
{
lean_object* v_a_6433_; lean_object* v_snd_6434_; 
v_a_6433_ = lean_ctor_get(v___x_6432_, 0);
lean_inc(v_a_6433_);
lean_dec_ref(v___x_6432_);
v_snd_6434_ = lean_ctor_get(v_a_6433_, 1);
lean_inc(v_snd_6434_);
lean_dec(v_a_6433_);
v_as_x27_6379_ = v_tail_6385_;
v_b_6380_ = v___x_6387_;
v___y_6381_ = v_snd_6434_;
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
else
{
lean_dec(v_val_6396_);
v___y_6389_ = v___y_6381_;
goto v___jp_6388_;
}
}
else
{
lean_dec(v___x_6395_);
v___y_6389_ = v___y_6381_;
goto v___jp_6388_;
}
v___jp_6388_:
{
lean_object* v___x_6390_; lean_object* v___x_6391_; 
v___x_6390_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0);
v___x_6391_ = l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(v___x_6390_, v___y_6389_);
if (lean_obj_tag(v___x_6391_) == 0)
{
lean_dec(v_snd_6378_);
lean_dec_ref(v___x_6377_);
lean_dec(v___x_6376_);
lean_dec_ref(v_a_6374_);
return v___x_6391_;
}
else
{
lean_object* v_a_6392_; lean_object* v_snd_6393_; 
v_a_6392_ = lean_ctor_get(v___x_6391_, 0);
lean_inc(v_a_6392_);
lean_dec_ref(v___x_6391_);
v_snd_6393_ = lean_ctor_get(v_a_6392_, 1);
lean_inc(v_snd_6393_);
lean_dec(v_a_6392_);
v_as_x27_6379_ = v_tail_6385_;
v_b_6380_ = v___x_6387_;
v___y_6381_ = v_snd_6393_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___boxed(lean_object* v_a_6496_, lean_object* v_allowPrimitive_6497_, lean_object* v___x_6498_, lean_object* v___x_6499_, lean_object* v_snd_6500_, lean_object* v_as_x27_6501_, lean_object* v_b_6502_, lean_object* v___y_6503_){
_start:
{
uint8_t v_allowPrimitive_boxed_6504_; lean_object* v_res_6505_; 
v_allowPrimitive_boxed_6504_ = lean_unbox(v_allowPrimitive_6497_);
v_res_6505_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg(v_a_6496_, v_allowPrimitive_boxed_6504_, v___x_6498_, v___x_6499_, v_snd_6500_, v_as_x27_6501_, v_b_6502_, v___y_6503_);
lean_dec(v_as_x27_6501_);
return v_res_6505_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___redArg(lean_object* v_a_6506_, uint8_t v_allowPrimitive_6507_, lean_object* v___x_6508_, lean_object* v___x_6509_, lean_object* v_snd_6510_, lean_object* v_as_6511_, lean_object* v_as_x27_6512_, lean_object* v_b_6513_, lean_object* v___y_6514_){
_start:
{
if (lean_obj_tag(v_as_x27_6512_) == 0)
{
lean_object* v___x_6515_; lean_object* v___x_6516_; 
lean_dec(v_snd_6510_);
lean_dec_ref(v___x_6509_);
lean_dec(v___x_6508_);
lean_dec_ref(v_a_6506_);
v___x_6515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_6515_, 0, v_b_6513_);
lean_ctor_set(v___x_6515_, 1, v___y_6514_);
v___x_6516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6516_, 0, v___x_6515_);
return v___x_6516_;
}
else
{
lean_object* v_head_6517_; lean_object* v_tail_6518_; lean_object* v_name_6519_; lean_object* v___x_6520_; lean_object* v___y_6522_; lean_object* v___x_6528_; 
v_head_6517_ = lean_ctor_get(v_as_x27_6512_, 0);
v_tail_6518_ = lean_ctor_get(v_as_x27_6512_, 1);
v_name_6519_ = lean_ctor_get(v_head_6517_, 0);
v___x_6520_ = lean_box(0);
lean_inc(v_name_6519_);
lean_inc_ref(v_a_6506_);
v___x_6528_ = lean_environment_find(v_a_6506_, v_name_6519_);
if (lean_obj_tag(v___x_6528_) == 1)
{
lean_object* v_val_6529_; 
v_val_6529_ = lean_ctor_get(v___x_6528_, 0);
lean_inc(v_val_6529_);
lean_dec_ref(v___x_6528_);
if (lean_obj_tag(v_val_6529_) == 5)
{
lean_object* v_val_6530_; lean_object* v___x_6532_; uint8_t v_isShared_6533_; uint8_t v_isSharedCheck_6628_; 
v_val_6530_ = lean_ctor_get(v_val_6529_, 0);
v_isSharedCheck_6628_ = !lean_is_exclusive(v_val_6529_);
if (v_isSharedCheck_6628_ == 0)
{
v___x_6532_ = v_val_6529_;
v_isShared_6533_ = v_isSharedCheck_6628_;
goto v_resetjp_6531_;
}
else
{
lean_inc(v_val_6530_);
lean_dec(v_val_6529_);
v___x_6532_ = lean_box(0);
v_isShared_6533_ = v_isSharedCheck_6628_;
goto v_resetjp_6531_;
}
v_resetjp_6531_:
{
lean_object* v_toConstantVal_6534_; lean_object* v_numParams_6535_; lean_object* v_numIndices_6536_; lean_object* v_ctors_6537_; lean_object* v_numNested_6538_; uint8_t v_isRec_6539_; uint8_t v_isUnsafe_6540_; uint8_t v_isReflexive_6541_; lean_object* v___x_6543_; uint8_t v_isShared_6544_; uint8_t v_isSharedCheck_6626_; 
v_toConstantVal_6534_ = lean_ctor_get(v_val_6530_, 0);
v_numParams_6535_ = lean_ctor_get(v_val_6530_, 1);
v_numIndices_6536_ = lean_ctor_get(v_val_6530_, 2);
v_ctors_6537_ = lean_ctor_get(v_val_6530_, 4);
v_numNested_6538_ = lean_ctor_get(v_val_6530_, 5);
v_isRec_6539_ = lean_ctor_get_uint8(v_val_6530_, sizeof(void*)*6);
v_isUnsafe_6540_ = lean_ctor_get_uint8(v_val_6530_, sizeof(void*)*6 + 1);
v_isReflexive_6541_ = lean_ctor_get_uint8(v_val_6530_, sizeof(void*)*6 + 2);
v_isSharedCheck_6626_ = !lean_is_exclusive(v_val_6530_);
if (v_isSharedCheck_6626_ == 0)
{
lean_object* v_unused_6627_; 
v_unused_6627_ = lean_ctor_get(v_val_6530_, 3);
lean_dec(v_unused_6627_);
v___x_6543_ = v_val_6530_;
v_isShared_6544_ = v_isSharedCheck_6626_;
goto v_resetjp_6542_;
}
else
{
lean_inc(v_numNested_6538_);
lean_inc(v_ctors_6537_);
lean_inc(v_numIndices_6536_);
lean_inc(v_numParams_6535_);
lean_inc(v_toConstantVal_6534_);
lean_dec(v_val_6530_);
v___x_6543_ = lean_box(0);
v_isShared_6544_ = v_isSharedCheck_6626_;
goto v_resetjp_6542_;
}
v_resetjp_6542_:
{
lean_object* v_name_6545_; lean_object* v___x_6546_; 
v_name_6545_ = lean_ctor_get(v_toConstantVal_6534_, 0);
lean_inc(v_name_6545_);
lean_inc_ref(v___y_6514_);
v___x_6546_ = l_Lean_Kernel_Environment_checkName(v___y_6514_, v_name_6545_, v_allowPrimitive_6507_);
if (lean_obj_tag(v___x_6546_) == 0)
{
lean_object* v_a_6547_; lean_object* v___x_6549_; uint8_t v_isShared_6550_; uint8_t v_isSharedCheck_6554_; 
lean_del_object(v___x_6543_);
lean_dec(v_numNested_6538_);
lean_dec(v_ctors_6537_);
lean_dec(v_numIndices_6536_);
lean_dec(v_numParams_6535_);
lean_dec_ref(v_toConstantVal_6534_);
lean_del_object(v___x_6532_);
lean_dec_ref(v___y_6514_);
lean_dec(v_snd_6510_);
lean_dec_ref(v___x_6509_);
lean_dec(v___x_6508_);
lean_dec_ref(v_a_6506_);
v_a_6547_ = lean_ctor_get(v___x_6546_, 0);
v_isSharedCheck_6554_ = !lean_is_exclusive(v___x_6546_);
if (v_isSharedCheck_6554_ == 0)
{
v___x_6549_ = v___x_6546_;
v_isShared_6550_ = v_isSharedCheck_6554_;
goto v_resetjp_6548_;
}
else
{
lean_inc(v_a_6547_);
lean_dec(v___x_6546_);
v___x_6549_ = lean_box(0);
v_isShared_6550_ = v_isSharedCheck_6554_;
goto v_resetjp_6548_;
}
v_resetjp_6548_:
{
lean_object* v___x_6552_; 
if (v_isShared_6550_ == 0)
{
v___x_6552_ = v___x_6549_;
goto v_reusejp_6551_;
}
else
{
lean_object* v_reuseFailAlloc_6553_; 
v_reuseFailAlloc_6553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6553_, 0, v_a_6547_);
v___x_6552_ = v_reuseFailAlloc_6553_;
goto v_reusejp_6551_;
}
v_reusejp_6551_:
{
return v___x_6552_;
}
}
}
else
{
lean_object* v___x_6556_; 
lean_dec_ref(v___x_6546_);
lean_inc(v_ctors_6537_);
lean_inc(v___x_6508_);
if (v_isShared_6544_ == 0)
{
lean_ctor_set(v___x_6543_, 3, v___x_6508_);
v___x_6556_ = v___x_6543_;
goto v_reusejp_6555_;
}
else
{
lean_object* v_reuseFailAlloc_6625_; 
v_reuseFailAlloc_6625_ = lean_alloc_ctor(0, 6, 3);
lean_ctor_set(v_reuseFailAlloc_6625_, 0, v_toConstantVal_6534_);
lean_ctor_set(v_reuseFailAlloc_6625_, 1, v_numParams_6535_);
lean_ctor_set(v_reuseFailAlloc_6625_, 2, v_numIndices_6536_);
lean_ctor_set(v_reuseFailAlloc_6625_, 3, v___x_6508_);
lean_ctor_set(v_reuseFailAlloc_6625_, 4, v_ctors_6537_);
lean_ctor_set(v_reuseFailAlloc_6625_, 5, v_numNested_6538_);
lean_ctor_set_uint8(v_reuseFailAlloc_6625_, sizeof(void*)*6, v_isRec_6539_);
lean_ctor_set_uint8(v_reuseFailAlloc_6625_, sizeof(void*)*6 + 1, v_isUnsafe_6540_);
lean_ctor_set_uint8(v_reuseFailAlloc_6625_, sizeof(void*)*6 + 2, v_isReflexive_6541_);
v___x_6556_ = v_reuseFailAlloc_6625_;
goto v_reusejp_6555_;
}
v_reusejp_6555_:
{
lean_object* v___x_6558_; 
if (v_isShared_6533_ == 0)
{
lean_ctor_set(v___x_6532_, 0, v___x_6556_);
v___x_6558_ = v___x_6532_;
goto v_reusejp_6557_;
}
else
{
lean_object* v_reuseFailAlloc_6624_; 
v_reuseFailAlloc_6624_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6624_, 0, v___x_6556_);
v___x_6558_ = v_reuseFailAlloc_6624_;
goto v_reusejp_6557_;
}
v_reusejp_6557_:
{
lean_object* v___x_6559_; lean_object* v___x_6560_; 
v___x_6559_ = lean_environment_add(v___y_6514_, v___x_6558_);
lean_inc_ref(v___x_6509_);
lean_inc_ref(v_a_6506_);
v___x_6560_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg(v_a_6506_, v_allowPrimitive_6507_, v___x_6509_, v_ctors_6537_, v___x_6520_, v___x_6559_);
lean_dec(v_ctors_6537_);
if (lean_obj_tag(v___x_6560_) == 0)
{
lean_dec(v_snd_6510_);
lean_dec_ref(v___x_6509_);
lean_dec(v___x_6508_);
lean_dec_ref(v_a_6506_);
return v___x_6560_;
}
else
{
lean_object* v_a_6561_; lean_object* v_snd_6562_; lean_object* v___x_6569_; lean_object* v___x_6570_; lean_object* v___x_6571_; 
v_a_6561_ = lean_ctor_get(v___x_6560_, 0);
lean_inc(v_a_6561_);
lean_dec_ref(v___x_6560_);
v_snd_6562_ = lean_ctor_get(v_a_6561_, 1);
lean_inc(v_snd_6562_);
lean_dec(v_a_6561_);
lean_inc(v_name_6519_);
v___x_6569_ = l_Lean_mkRecName(v_name_6519_);
v___x_6570_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(v_snd_6510_, v___x_6569_, v___x_6569_);
lean_inc(v___x_6569_);
lean_inc_ref(v_a_6506_);
v___x_6571_ = lean_environment_find(v_a_6506_, v___x_6569_);
if (lean_obj_tag(v___x_6571_) == 1)
{
lean_object* v_val_6572_; 
v_val_6572_ = lean_ctor_get(v___x_6571_, 0);
lean_inc(v_val_6572_);
lean_dec_ref(v___x_6571_);
if (lean_obj_tag(v_val_6572_) == 7)
{
lean_object* v_val_6573_; lean_object* v___x_6575_; uint8_t v_isShared_6576_; uint8_t v_isSharedCheck_6623_; 
v_val_6573_ = lean_ctor_get(v_val_6572_, 0);
v_isSharedCheck_6623_ = !lean_is_exclusive(v_val_6572_);
if (v_isSharedCheck_6623_ == 0)
{
v___x_6575_ = v_val_6572_;
v_isShared_6576_ = v_isSharedCheck_6623_;
goto v_resetjp_6574_;
}
else
{
lean_inc(v_val_6573_);
lean_dec(v_val_6572_);
v___x_6575_ = lean_box(0);
v_isShared_6576_ = v_isSharedCheck_6623_;
goto v_resetjp_6574_;
}
v_resetjp_6574_:
{
lean_object* v_toConstantVal_6577_; lean_object* v_numParams_6578_; lean_object* v_numIndices_6579_; lean_object* v_numMotives_6580_; lean_object* v_numMinors_6581_; lean_object* v_rules_6582_; uint8_t v_k_6583_; uint8_t v_isUnsafe_6584_; lean_object* v___x_6586_; uint8_t v_isShared_6587_; uint8_t v_isSharedCheck_6621_; 
v_toConstantVal_6577_ = lean_ctor_get(v_val_6573_, 0);
v_numParams_6578_ = lean_ctor_get(v_val_6573_, 2);
v_numIndices_6579_ = lean_ctor_get(v_val_6573_, 3);
v_numMotives_6580_ = lean_ctor_get(v_val_6573_, 4);
v_numMinors_6581_ = lean_ctor_get(v_val_6573_, 5);
v_rules_6582_ = lean_ctor_get(v_val_6573_, 6);
v_k_6583_ = lean_ctor_get_uint8(v_val_6573_, sizeof(void*)*7);
v_isUnsafe_6584_ = lean_ctor_get_uint8(v_val_6573_, sizeof(void*)*7 + 1);
v_isSharedCheck_6621_ = !lean_is_exclusive(v_val_6573_);
if (v_isSharedCheck_6621_ == 0)
{
lean_object* v_unused_6622_; 
v_unused_6622_ = lean_ctor_get(v_val_6573_, 1);
lean_dec(v_unused_6622_);
v___x_6586_ = v_val_6573_;
v_isShared_6587_ = v_isSharedCheck_6621_;
goto v_resetjp_6585_;
}
else
{
lean_inc(v_rules_6582_);
lean_inc(v_numMinors_6581_);
lean_inc(v_numMotives_6580_);
lean_inc(v_numIndices_6579_);
lean_inc(v_numParams_6578_);
lean_inc(v_toConstantVal_6577_);
lean_dec(v_val_6573_);
v___x_6586_ = lean_box(0);
v_isShared_6587_ = v_isSharedCheck_6621_;
goto v_resetjp_6585_;
}
v_resetjp_6585_:
{
lean_object* v___x_6588_; lean_object* v___x_6589_; lean_object* v_a_6590_; lean_object* v_fst_6591_; lean_object* v_snd_6592_; lean_object* v___x_6593_; 
v___x_6588_ = lean_box(0);
lean_inc(v_snd_6510_);
lean_inc_ref(v_a_6506_);
lean_inc_ref(v___x_6509_);
v___x_6589_ = l_List_mapM_loop___at___00Lean4Lean_Environment_addInductive_spec__3(v___x_6509_, v_a_6506_, v_snd_6510_, v___x_6570_, v___x_6569_, v_rules_6582_, v___x_6588_, v_snd_6562_);
lean_dec(v___x_6569_);
v_a_6590_ = lean_ctor_get(v___x_6589_, 0);
lean_inc(v_a_6590_);
lean_dec_ref(v___x_6589_);
v_fst_6591_ = lean_ctor_get(v_a_6590_, 0);
lean_inc(v_fst_6591_);
v_snd_6592_ = lean_ctor_get(v_a_6590_, 1);
lean_inc_n(v_snd_6592_, 2);
lean_dec(v_a_6590_);
lean_inc(v___x_6570_);
v___x_6593_ = l_Lean_Kernel_Environment_checkName(v_snd_6592_, v___x_6570_, v_allowPrimitive_6507_);
if (lean_obj_tag(v___x_6593_) == 0)
{
lean_object* v_a_6594_; lean_object* v___x_6596_; uint8_t v_isShared_6597_; uint8_t v_isSharedCheck_6601_; 
lean_dec(v_snd_6592_);
lean_dec(v_fst_6591_);
lean_del_object(v___x_6586_);
lean_dec(v_numMinors_6581_);
lean_dec(v_numMotives_6580_);
lean_dec(v_numIndices_6579_);
lean_dec(v_numParams_6578_);
lean_dec_ref(v_toConstantVal_6577_);
lean_del_object(v___x_6575_);
lean_dec(v___x_6570_);
lean_dec(v_snd_6510_);
lean_dec_ref(v___x_6509_);
lean_dec(v___x_6508_);
lean_dec_ref(v_a_6506_);
v_a_6594_ = lean_ctor_get(v___x_6593_, 0);
v_isSharedCheck_6601_ = !lean_is_exclusive(v___x_6593_);
if (v_isSharedCheck_6601_ == 0)
{
v___x_6596_ = v___x_6593_;
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
else
{
lean_inc(v_a_6594_);
lean_dec(v___x_6593_);
v___x_6596_ = lean_box(0);
v_isShared_6597_ = v_isSharedCheck_6601_;
goto v_resetjp_6595_;
}
v_resetjp_6595_:
{
lean_object* v___x_6599_; 
if (v_isShared_6597_ == 0)
{
v___x_6599_ = v___x_6596_;
goto v_reusejp_6598_;
}
else
{
lean_object* v_reuseFailAlloc_6600_; 
v_reuseFailAlloc_6600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6600_, 0, v_a_6594_);
v___x_6599_ = v_reuseFailAlloc_6600_;
goto v_reusejp_6598_;
}
v_reusejp_6598_:
{
return v___x_6599_;
}
}
}
else
{
lean_object* v_levelParams_6602_; lean_object* v_type_6603_; lean_object* v___x_6605_; uint8_t v_isShared_6606_; uint8_t v_isSharedCheck_6619_; 
lean_dec_ref(v___x_6593_);
v_levelParams_6602_ = lean_ctor_get(v_toConstantVal_6577_, 1);
v_type_6603_ = lean_ctor_get(v_toConstantVal_6577_, 2);
v_isSharedCheck_6619_ = !lean_is_exclusive(v_toConstantVal_6577_);
if (v_isSharedCheck_6619_ == 0)
{
lean_object* v_unused_6620_; 
v_unused_6620_ = lean_ctor_get(v_toConstantVal_6577_, 0);
lean_dec(v_unused_6620_);
v___x_6605_ = v_toConstantVal_6577_;
v_isShared_6606_ = v_isSharedCheck_6619_;
goto v_resetjp_6604_;
}
else
{
lean_inc(v_type_6603_);
lean_inc(v_levelParams_6602_);
lean_dec(v_toConstantVal_6577_);
v___x_6605_ = lean_box(0);
v_isShared_6606_ = v_isSharedCheck_6619_;
goto v_resetjp_6604_;
}
v_resetjp_6604_:
{
lean_object* v___x_6607_; lean_object* v___x_6609_; 
lean_inc(v_snd_6510_);
lean_inc_ref(v_a_6506_);
lean_inc_ref(v___x_6509_);
v___x_6607_ = l_Lean4Lean_ElimNestedInductive_Result_restoreNested(v___x_6509_, v_a_6506_, v_type_6603_, v_snd_6510_);
if (v_isShared_6606_ == 0)
{
lean_ctor_set(v___x_6605_, 2, v___x_6607_);
lean_ctor_set(v___x_6605_, 0, v___x_6570_);
v___x_6609_ = v___x_6605_;
goto v_reusejp_6608_;
}
else
{
lean_object* v_reuseFailAlloc_6618_; 
v_reuseFailAlloc_6618_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_6618_, 0, v___x_6570_);
lean_ctor_set(v_reuseFailAlloc_6618_, 1, v_levelParams_6602_);
lean_ctor_set(v_reuseFailAlloc_6618_, 2, v___x_6607_);
v___x_6609_ = v_reuseFailAlloc_6618_;
goto v_reusejp_6608_;
}
v_reusejp_6608_:
{
lean_object* v___x_6611_; 
lean_inc(v___x_6508_);
if (v_isShared_6587_ == 0)
{
lean_ctor_set(v___x_6586_, 6, v_fst_6591_);
lean_ctor_set(v___x_6586_, 1, v___x_6508_);
lean_ctor_set(v___x_6586_, 0, v___x_6609_);
v___x_6611_ = v___x_6586_;
goto v_reusejp_6610_;
}
else
{
lean_object* v_reuseFailAlloc_6617_; 
v_reuseFailAlloc_6617_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v_reuseFailAlloc_6617_, 0, v___x_6609_);
lean_ctor_set(v_reuseFailAlloc_6617_, 1, v___x_6508_);
lean_ctor_set(v_reuseFailAlloc_6617_, 2, v_numParams_6578_);
lean_ctor_set(v_reuseFailAlloc_6617_, 3, v_numIndices_6579_);
lean_ctor_set(v_reuseFailAlloc_6617_, 4, v_numMotives_6580_);
lean_ctor_set(v_reuseFailAlloc_6617_, 5, v_numMinors_6581_);
lean_ctor_set(v_reuseFailAlloc_6617_, 6, v_fst_6591_);
lean_ctor_set_uint8(v_reuseFailAlloc_6617_, sizeof(void*)*7, v_k_6583_);
lean_ctor_set_uint8(v_reuseFailAlloc_6617_, sizeof(void*)*7 + 1, v_isUnsafe_6584_);
v___x_6611_ = v_reuseFailAlloc_6617_;
goto v_reusejp_6610_;
}
v_reusejp_6610_:
{
lean_object* v___x_6613_; 
if (v_isShared_6576_ == 0)
{
lean_ctor_set(v___x_6575_, 0, v___x_6611_);
v___x_6613_ = v___x_6575_;
goto v_reusejp_6612_;
}
else
{
lean_object* v_reuseFailAlloc_6616_; 
v_reuseFailAlloc_6616_ = lean_alloc_ctor(7, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6616_, 0, v___x_6611_);
v___x_6613_ = v_reuseFailAlloc_6616_;
goto v_reusejp_6612_;
}
v_reusejp_6612_:
{
lean_object* v___x_6614_; lean_object* v___x_6615_; 
v___x_6614_ = lean_environment_add(v_snd_6592_, v___x_6613_);
v___x_6615_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg(v_a_6506_, v_allowPrimitive_6507_, v___x_6508_, v___x_6509_, v_snd_6510_, v_tail_6518_, v___x_6520_, v___x_6614_);
return v___x_6615_;
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
lean_dec(v_val_6572_);
lean_dec(v___x_6570_);
lean_dec(v___x_6569_);
goto v___jp_6563_;
}
}
else
{
lean_dec(v___x_6571_);
lean_dec(v___x_6570_);
lean_dec(v___x_6569_);
goto v___jp_6563_;
}
v___jp_6563_:
{
lean_object* v___x_6564_; lean_object* v___x_6565_; 
v___x_6564_ = lean_obj_once(&l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1, &l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1_once, _init_l_List_forM___at___00List_forM___at___00Lean4Lean_Environment_addInductive_spec__6_spec__7___closed__1);
v___x_6565_ = l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(v___x_6564_, v_snd_6562_);
if (lean_obj_tag(v___x_6565_) == 0)
{
lean_dec(v_snd_6510_);
lean_dec_ref(v___x_6509_);
lean_dec(v___x_6508_);
lean_dec_ref(v_a_6506_);
return v___x_6565_;
}
else
{
lean_object* v_a_6566_; lean_object* v_snd_6567_; lean_object* v___x_6568_; 
v_a_6566_ = lean_ctor_get(v___x_6565_, 0);
lean_inc(v_a_6566_);
lean_dec_ref(v___x_6565_);
v_snd_6567_ = lean_ctor_get(v_a_6566_, 1);
lean_inc(v_snd_6567_);
lean_dec(v_a_6566_);
v___x_6568_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg(v_a_6506_, v_allowPrimitive_6507_, v___x_6508_, v___x_6509_, v_snd_6510_, v_tail_6518_, v___x_6520_, v_snd_6567_);
return v___x_6568_;
}
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
lean_dec(v_val_6529_);
v___y_6522_ = v___y_6514_;
goto v___jp_6521_;
}
}
else
{
lean_dec(v___x_6528_);
v___y_6522_ = v___y_6514_;
goto v___jp_6521_;
}
v___jp_6521_:
{
lean_object* v___x_6523_; lean_object* v___x_6524_; 
v___x_6523_ = lean_obj_once(&l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0, &l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg___closed__0);
v___x_6524_ = l_panic___at___00Lean4Lean_Environment_addInductive_spec__1(v___x_6523_, v___y_6522_);
if (lean_obj_tag(v___x_6524_) == 0)
{
lean_dec(v_snd_6510_);
lean_dec_ref(v___x_6509_);
lean_dec(v___x_6508_);
lean_dec_ref(v_a_6506_);
return v___x_6524_;
}
else
{
lean_object* v_a_6525_; lean_object* v_snd_6526_; lean_object* v___x_6527_; 
v_a_6525_ = lean_ctor_get(v___x_6524_, 0);
lean_inc(v_a_6525_);
lean_dec_ref(v___x_6524_);
v_snd_6526_ = lean_ctor_get(v_a_6525_, 1);
lean_inc(v_snd_6526_);
lean_dec(v_a_6525_);
v___x_6527_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg(v_a_6506_, v_allowPrimitive_6507_, v___x_6508_, v___x_6509_, v_snd_6510_, v_tail_6518_, v___x_6520_, v_snd_6526_);
return v___x_6527_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___redArg___boxed(lean_object* v_a_6629_, lean_object* v_allowPrimitive_6630_, lean_object* v___x_6631_, lean_object* v___x_6632_, lean_object* v_snd_6633_, lean_object* v_as_6634_, lean_object* v_as_x27_6635_, lean_object* v_b_6636_, lean_object* v___y_6637_){
_start:
{
uint8_t v_allowPrimitive_boxed_6638_; lean_object* v_res_6639_; 
v_allowPrimitive_boxed_6638_ = lean_unbox(v_allowPrimitive_6630_);
v_res_6639_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___redArg(v_a_6629_, v_allowPrimitive_boxed_6638_, v___x_6631_, v___x_6632_, v_snd_6633_, v_as_6634_, v_as_x27_6635_, v_b_6636_, v___y_6637_);
lean_dec(v_as_x27_6635_);
lean_dec(v_as_6634_);
return v_res_6639_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean4Lean_Environment_addInductive_spec__0(lean_object* v_a_6640_, lean_object* v_a_6641_){
_start:
{
if (lean_obj_tag(v_a_6640_) == 0)
{
lean_object* v___x_6642_; 
v___x_6642_ = l_List_reverse___redArg(v_a_6641_);
return v___x_6642_;
}
else
{
lean_object* v_head_6643_; lean_object* v_tail_6644_; lean_object* v___x_6646_; uint8_t v_isShared_6647_; uint8_t v_isSharedCheck_6653_; 
v_head_6643_ = lean_ctor_get(v_a_6640_, 0);
v_tail_6644_ = lean_ctor_get(v_a_6640_, 1);
v_isSharedCheck_6653_ = !lean_is_exclusive(v_a_6640_);
if (v_isSharedCheck_6653_ == 0)
{
v___x_6646_ = v_a_6640_;
v_isShared_6647_ = v_isSharedCheck_6653_;
goto v_resetjp_6645_;
}
else
{
lean_inc(v_tail_6644_);
lean_inc(v_head_6643_);
lean_dec(v_a_6640_);
v___x_6646_ = lean_box(0);
v_isShared_6647_ = v_isSharedCheck_6653_;
goto v_resetjp_6645_;
}
v_resetjp_6645_:
{
lean_object* v_name_6648_; lean_object* v___x_6650_; 
v_name_6648_ = lean_ctor_get(v_head_6643_, 0);
lean_inc(v_name_6648_);
lean_dec(v_head_6643_);
if (v_isShared_6647_ == 0)
{
lean_ctor_set(v___x_6646_, 1, v_a_6641_);
lean_ctor_set(v___x_6646_, 0, v_name_6648_);
v___x_6650_ = v___x_6646_;
goto v_reusejp_6649_;
}
else
{
lean_object* v_reuseFailAlloc_6652_; 
v_reuseFailAlloc_6652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6652_, 0, v_name_6648_);
lean_ctor_set(v_reuseFailAlloc_6652_, 1, v_a_6641_);
v___x_6650_ = v_reuseFailAlloc_6652_;
goto v_reusejp_6649_;
}
v_reusejp_6649_:
{
v_a_6640_ = v_tail_6644_;
v_a_6641_ = v___x_6650_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_addInductive(lean_object* v_env_6660_, lean_object* v_lparams_6661_, lean_object* v_nparams_6662_, lean_object* v_types_6663_, uint8_t v_isUnsafe_6664_, uint8_t v_allowPrimitive_6665_){
_start:
{
lean_object* v___y_6667_; lean_object* v___x_6685_; lean_object* v___x_6686_; lean_object* v___x_6687_; lean_object* v___x_6688_; lean_object* v___x_6689_; lean_object* v___x_6690_; lean_object* v___x_6691_; lean_object* v___x_6692_; lean_object* v___x_6693_; 
v___x_6685_ = lean_unsigned_to_nat(1u);
v___x_6686_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_Result_restoreNested___closed__3));
v___x_6687_ = lean_unsigned_to_nat(0u);
v___x_6688_ = ((lean_object*)(l_Lean4Lean_ElimNestedInductive_instInhabitedState_default___closed__0));
v___x_6689_ = lean_box(0);
lean_inc(v_lparams_6661_);
v___x_6690_ = l_List_mapTR_loop___at___00Lean4Lean_AddInductive_checkInductiveTypes_spec__0(v_lparams_6661_, v___x_6689_);
lean_inc_n(v_types_6663_, 2);
v___x_6691_ = lean_array_mk(v_types_6663_);
v___x_6692_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6692_, 0, v___x_6686_);
lean_ctor_set(v___x_6692_, 1, v___x_6688_);
lean_ctor_set(v___x_6692_, 2, v___x_6690_);
lean_ctor_set(v___x_6692_, 3, v___x_6691_);
lean_ctor_set(v___x_6692_, 4, v___x_6685_);
lean_inc(v_nparams_6662_);
v___x_6693_ = l_Lean4Lean_ElimNestedInductive_run(v_nparams_6662_, v_types_6663_, v_env_6660_, v___x_6692_);
if (lean_obj_tag(v___x_6693_) == 0)
{
lean_object* v_a_6694_; lean_object* v___x_6696_; uint8_t v_isShared_6697_; uint8_t v_isSharedCheck_6701_; 
lean_dec(v_types_6663_);
lean_dec(v_nparams_6662_);
lean_dec(v_lparams_6661_);
lean_dec_ref(v_env_6660_);
v_a_6694_ = lean_ctor_get(v___x_6693_, 0);
v_isSharedCheck_6701_ = !lean_is_exclusive(v___x_6693_);
if (v_isSharedCheck_6701_ == 0)
{
v___x_6696_ = v___x_6693_;
v_isShared_6697_ = v_isSharedCheck_6701_;
goto v_resetjp_6695_;
}
else
{
lean_inc(v_a_6694_);
lean_dec(v___x_6693_);
v___x_6696_ = lean_box(0);
v_isShared_6697_ = v_isSharedCheck_6701_;
goto v_resetjp_6695_;
}
v_resetjp_6695_:
{
lean_object* v___x_6699_; 
if (v_isShared_6697_ == 0)
{
v___x_6699_ = v___x_6696_;
goto v_reusejp_6698_;
}
else
{
lean_object* v_reuseFailAlloc_6700_; 
v_reuseFailAlloc_6700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6700_, 0, v_a_6694_);
v___x_6699_ = v_reuseFailAlloc_6700_;
goto v_reusejp_6698_;
}
v_reusejp_6698_:
{
return v___x_6699_;
}
}
}
else
{
lean_object* v_a_6702_; lean_object* v_fst_6703_; lean_object* v___y_6705_; lean_object* v___y_6706_; uint8_t v___y_6707_; lean_object* v___y_6708_; lean_object* v___y_6709_; uint8_t v___y_6710_; lean_object* v_aux2nested_6723_; lean_object* v_types_6724_; lean_object* v___y_6726_; 
v_a_6702_ = lean_ctor_get(v___x_6693_, 0);
lean_inc(v_a_6702_);
lean_dec_ref(v___x_6693_);
v_fst_6703_ = lean_ctor_get(v_a_6702_, 0);
lean_inc(v_fst_6703_);
lean_dec(v_a_6702_);
v_aux2nested_6723_ = lean_ctor_get(v_fst_6703_, 2);
v_types_6724_ = lean_ctor_get(v_fst_6703_, 3);
if (lean_obj_tag(v_aux2nested_6723_) == 0)
{
lean_object* v_size_6732_; 
v_size_6732_ = lean_ctor_get(v_aux2nested_6723_, 0);
lean_inc(v_size_6732_);
v___y_6726_ = v_size_6732_;
goto v___jp_6725_;
}
else
{
v___y_6726_ = v___x_6687_;
goto v___jp_6725_;
}
v___jp_6704_:
{
lean_object* v___x_6711_; lean_object* v___x_6712_; 
lean_inc_ref(v___y_6709_);
lean_inc_ref(v___y_6706_);
lean_inc_ref(v_env_6660_);
v___x_6711_ = lean_alloc_ctor(0, 4, 2);
lean_ctor_set(v___x_6711_, 0, v_env_6660_);
lean_ctor_set(v___x_6711_, 1, v___y_6706_);
lean_ctor_set(v___x_6711_, 2, v_lparams_6661_);
lean_ctor_set(v___x_6711_, 3, v___y_6709_);
lean_ctor_set_uint8(v___x_6711_, sizeof(void*)*4, v___y_6710_);
lean_ctor_set_uint8(v___x_6711_, sizeof(void*)*4 + 1, v_allowPrimitive_6665_);
v___x_6712_ = l_Lean4Lean_AddInductive_run(v_nparams_6662_, v___y_6708_, v___y_6705_, v___x_6711_);
lean_dec_ref(v___x_6711_);
if (lean_obj_tag(v___x_6712_) == 0)
{
lean_dec(v_fst_6703_);
lean_dec(v_types_6663_);
lean_dec_ref(v_env_6660_);
return v___x_6712_;
}
else
{
if (v___y_6707_ == 0)
{
lean_object* v_a_6713_; lean_object* v___x_6714_; lean_object* v___x_6715_; lean_object* v_fst_6716_; lean_object* v_snd_6717_; lean_object* v___x_6718_; lean_object* v___x_6719_; 
v_a_6713_ = lean_ctor_get(v___x_6712_, 0);
lean_inc_n(v_a_6713_, 3);
lean_dec_ref(v___x_6712_);
lean_inc_n(v_types_6663_, 2);
v___x_6714_ = l_List_mapTR_loop___at___00Lean4Lean_Environment_addInductive_spec__0(v_types_6663_, v___x_6689_);
v___x_6715_ = l_Lean4Lean_mkAuxRecNameMap(v_a_6713_, v_types_6663_);
v_fst_6716_ = lean_ctor_get(v___x_6715_, 0);
lean_inc(v_fst_6716_);
v_snd_6717_ = lean_ctor_get(v___x_6715_, 1);
lean_inc_n(v_snd_6717_, 2);
lean_dec_ref(v___x_6715_);
v___x_6718_ = lean_box(0);
lean_inc(v_fst_6703_);
lean_inc(v___x_6714_);
v___x_6719_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___redArg(v_a_6713_, v_allowPrimitive_6665_, v___x_6714_, v_fst_6703_, v_snd_6717_, v_types_6663_, v_types_6663_, v___x_6718_, v_env_6660_);
lean_dec(v_types_6663_);
if (lean_obj_tag(v___x_6719_) == 0)
{
lean_dec(v_snd_6717_);
lean_dec(v_fst_6716_);
lean_dec(v___x_6714_);
lean_dec(v_a_6713_);
lean_dec(v_fst_6703_);
v___y_6667_ = v___x_6719_;
goto v___jp_6666_;
}
else
{
lean_object* v_a_6720_; lean_object* v_snd_6721_; lean_object* v___x_6722_; 
v_a_6720_ = lean_ctor_get(v___x_6719_, 0);
lean_inc(v_a_6720_);
lean_dec_ref(v___x_6719_);
v_snd_6721_ = lean_ctor_get(v_a_6720_, 1);
lean_inc(v_snd_6721_);
lean_dec(v_a_6720_);
v___x_6722_ = l_List_forM___at___00Lean4Lean_Environment_addInductive_spec__6(v_snd_6717_, v_fst_6703_, v_a_6713_, v_allowPrimitive_6665_, v___x_6714_, v_fst_6716_, v_snd_6721_);
v___y_6667_ = v___x_6722_;
goto v___jp_6666_;
}
}
else
{
lean_dec(v_fst_6703_);
lean_dec(v_types_6663_);
lean_dec_ref(v_env_6660_);
return v___x_6712_;
}
}
}
v___jp_6725_:
{
lean_object* v___x_6727_; lean_object* v___x_6728_; uint8_t v___x_6729_; 
v___x_6727_ = lean_obj_once(&l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4, &l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4_once, _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default___closed__4);
v___x_6728_ = ((lean_object*)(l_Lean4Lean_Environment_addInductive___closed__2));
v___x_6729_ = lean_nat_dec_eq(v___y_6726_, v___x_6687_);
if (v_isUnsafe_6664_ == 0)
{
uint8_t v___x_6730_; 
v___x_6730_ = 1;
lean_inc(v_types_6724_);
v___y_6705_ = v___y_6726_;
v___y_6706_ = v___x_6727_;
v___y_6707_ = v___x_6729_;
v___y_6708_ = v_types_6724_;
v___y_6709_ = v___x_6728_;
v___y_6710_ = v___x_6730_;
goto v___jp_6704_;
}
else
{
uint8_t v___x_6731_; 
v___x_6731_ = 0;
lean_inc(v_types_6724_);
v___y_6705_ = v___y_6726_;
v___y_6706_ = v___x_6727_;
v___y_6707_ = v___x_6729_;
v___y_6708_ = v_types_6724_;
v___y_6709_ = v___x_6728_;
v___y_6710_ = v___x_6731_;
goto v___jp_6704_;
}
}
}
v___jp_6666_:
{
if (lean_obj_tag(v___y_6667_) == 0)
{
lean_object* v_a_6668_; lean_object* v___x_6670_; uint8_t v_isShared_6671_; uint8_t v_isSharedCheck_6675_; 
v_a_6668_ = lean_ctor_get(v___y_6667_, 0);
v_isSharedCheck_6675_ = !lean_is_exclusive(v___y_6667_);
if (v_isSharedCheck_6675_ == 0)
{
v___x_6670_ = v___y_6667_;
v_isShared_6671_ = v_isSharedCheck_6675_;
goto v_resetjp_6669_;
}
else
{
lean_inc(v_a_6668_);
lean_dec(v___y_6667_);
v___x_6670_ = lean_box(0);
v_isShared_6671_ = v_isSharedCheck_6675_;
goto v_resetjp_6669_;
}
v_resetjp_6669_:
{
lean_object* v___x_6673_; 
if (v_isShared_6671_ == 0)
{
v___x_6673_ = v___x_6670_;
goto v_reusejp_6672_;
}
else
{
lean_object* v_reuseFailAlloc_6674_; 
v_reuseFailAlloc_6674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6674_, 0, v_a_6668_);
v___x_6673_ = v_reuseFailAlloc_6674_;
goto v_reusejp_6672_;
}
v_reusejp_6672_:
{
return v___x_6673_;
}
}
}
else
{
lean_object* v_a_6676_; lean_object* v___x_6678_; uint8_t v_isShared_6679_; uint8_t v_isSharedCheck_6684_; 
v_a_6676_ = lean_ctor_get(v___y_6667_, 0);
v_isSharedCheck_6684_ = !lean_is_exclusive(v___y_6667_);
if (v_isSharedCheck_6684_ == 0)
{
v___x_6678_ = v___y_6667_;
v_isShared_6679_ = v_isSharedCheck_6684_;
goto v_resetjp_6677_;
}
else
{
lean_inc(v_a_6676_);
lean_dec(v___y_6667_);
v___x_6678_ = lean_box(0);
v_isShared_6679_ = v_isSharedCheck_6684_;
goto v_resetjp_6677_;
}
v_resetjp_6677_:
{
lean_object* v_snd_6680_; lean_object* v___x_6682_; 
v_snd_6680_ = lean_ctor_get(v_a_6676_, 1);
lean_inc(v_snd_6680_);
lean_dec(v_a_6676_);
if (v_isShared_6679_ == 0)
{
lean_ctor_set(v___x_6678_, 0, v_snd_6680_);
v___x_6682_ = v___x_6678_;
goto v_reusejp_6681_;
}
else
{
lean_object* v_reuseFailAlloc_6683_; 
v_reuseFailAlloc_6683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6683_, 0, v_snd_6680_);
v___x_6682_ = v_reuseFailAlloc_6683_;
goto v_reusejp_6681_;
}
v_reusejp_6681_:
{
return v___x_6682_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_addInductive___boxed(lean_object* v_env_6733_, lean_object* v_lparams_6734_, lean_object* v_nparams_6735_, lean_object* v_types_6736_, lean_object* v_isUnsafe_6737_, lean_object* v_allowPrimitive_6738_){
_start:
{
uint8_t v_isUnsafe_boxed_6739_; uint8_t v_allowPrimitive_boxed_6740_; lean_object* v_res_6741_; 
v_isUnsafe_boxed_6739_ = lean_unbox(v_isUnsafe_6737_);
v_allowPrimitive_boxed_6740_ = lean_unbox(v_allowPrimitive_6738_);
v_res_6741_ = l_Lean4Lean_Environment_addInductive(v_env_6733_, v_lparams_6734_, v_nparams_6735_, v_types_6736_, v_isUnsafe_boxed_6739_, v_allowPrimitive_boxed_6740_);
return v_res_6741_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2(lean_object* v_00_u03b4_6742_, lean_object* v_t_6743_, lean_object* v_k_6744_, lean_object* v_fallback_6745_){
_start:
{
lean_object* v___x_6746_; 
v___x_6746_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___redArg(v_t_6743_, v_k_6744_, v_fallback_6745_);
return v___x_6746_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2___boxed(lean_object* v_00_u03b4_6747_, lean_object* v_t_6748_, lean_object* v_k_6749_, lean_object* v_fallback_6750_){
_start:
{
lean_object* v_res_6751_; 
v_res_6751_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean4Lean_Environment_addInductive_spec__2(v_00_u03b4_6747_, v_t_6748_, v_k_6749_, v_fallback_6750_);
lean_dec(v_fallback_6750_);
lean_dec(v_k_6749_);
lean_dec(v_t_6748_);
return v_res_6751_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4(lean_object* v_a_6752_, uint8_t v_allowPrimitive_6753_, lean_object* v___x_6754_, lean_object* v_as_6755_, lean_object* v_as_x27_6756_, lean_object* v_b_6757_, lean_object* v_a_6758_, lean_object* v___y_6759_){
_start:
{
lean_object* v___x_6760_; 
v___x_6760_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___redArg(v_a_6752_, v_allowPrimitive_6753_, v___x_6754_, v_as_x27_6756_, v_b_6757_, v___y_6759_);
return v___x_6760_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4___boxed(lean_object* v_a_6761_, lean_object* v_allowPrimitive_6762_, lean_object* v___x_6763_, lean_object* v_as_6764_, lean_object* v_as_x27_6765_, lean_object* v_b_6766_, lean_object* v_a_6767_, lean_object* v___y_6768_){
_start:
{
uint8_t v_allowPrimitive_boxed_6769_; lean_object* v_res_6770_; 
v_allowPrimitive_boxed_6769_ = lean_unbox(v_allowPrimitive_6762_);
v_res_6770_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__4(v_a_6761_, v_allowPrimitive_boxed_6769_, v___x_6763_, v_as_6764_, v_as_x27_6765_, v_b_6766_, v_a_6767_, v___y_6768_);
lean_dec(v_as_x27_6765_);
lean_dec(v_as_6764_);
return v_res_6770_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5(lean_object* v_a_6771_, uint8_t v_allowPrimitive_6772_, lean_object* v___x_6773_, lean_object* v___x_6774_, lean_object* v_snd_6775_, lean_object* v_as_6776_, lean_object* v_as_x27_6777_, lean_object* v_b_6778_, lean_object* v_a_6779_, lean_object* v___y_6780_){
_start:
{
lean_object* v___x_6781_; 
v___x_6781_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___redArg(v_a_6771_, v_allowPrimitive_6772_, v___x_6773_, v___x_6774_, v_snd_6775_, v_as_6776_, v_as_x27_6777_, v_b_6778_, v___y_6780_);
return v___x_6781_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5___boxed(lean_object* v_a_6782_, lean_object* v_allowPrimitive_6783_, lean_object* v___x_6784_, lean_object* v___x_6785_, lean_object* v_snd_6786_, lean_object* v_as_6787_, lean_object* v_as_x27_6788_, lean_object* v_b_6789_, lean_object* v_a_6790_, lean_object* v___y_6791_){
_start:
{
uint8_t v_allowPrimitive_boxed_6792_; lean_object* v_res_6793_; 
v_allowPrimitive_boxed_6792_ = lean_unbox(v_allowPrimitive_6783_);
v_res_6793_ = l_List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5(v_a_6782_, v_allowPrimitive_boxed_6792_, v___x_6784_, v___x_6785_, v_snd_6786_, v_as_6787_, v_as_x27_6788_, v_b_6789_, v_a_6790_, v___y_6791_);
lean_dec(v_as_x27_6788_);
lean_dec(v_as_6787_);
return v_res_6793_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5(lean_object* v_a_6794_, uint8_t v_allowPrimitive_6795_, lean_object* v___x_6796_, lean_object* v___x_6797_, lean_object* v_snd_6798_, lean_object* v_as_6799_, lean_object* v_as_x27_6800_, lean_object* v_b_6801_, lean_object* v_a_6802_, lean_object* v___y_6803_){
_start:
{
lean_object* v___x_6804_; 
v___x_6804_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___redArg(v_a_6794_, v_allowPrimitive_6795_, v___x_6796_, v___x_6797_, v_snd_6798_, v_as_x27_6800_, v_b_6801_, v___y_6803_);
return v___x_6804_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5___boxed(lean_object* v_a_6805_, lean_object* v_allowPrimitive_6806_, lean_object* v___x_6807_, lean_object* v___x_6808_, lean_object* v_snd_6809_, lean_object* v_as_6810_, lean_object* v_as_x27_6811_, lean_object* v_b_6812_, lean_object* v_a_6813_, lean_object* v___y_6814_){
_start:
{
uint8_t v_allowPrimitive_boxed_6815_; lean_object* v_res_6816_; 
v_allowPrimitive_boxed_6815_ = lean_unbox(v_allowPrimitive_6806_);
v_res_6816_ = l_List_forIn_x27_loop___at___00List_forIn_x27_loop___at___00Lean4Lean_Environment_addInductive_spec__5_spec__5(v_a_6805_, v_allowPrimitive_boxed_6815_, v___x_6807_, v___x_6808_, v_snd_6809_, v_as_6810_, v_as_x27_6811_, v_b_6812_, v_a_6813_, v___y_6814_);
lean_dec(v_as_x27_6811_);
lean_dec(v_as_6810_);
return v_res_6816_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Inductive_Add(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean4Lean_AddInductive_instInhabitedRecInfo_default = _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo_default();
lean_mark_persistent(l_Lean4Lean_AddInductive_instInhabitedRecInfo_default);
l_Lean4Lean_AddInductive_instInhabitedRecInfo = _init_l_Lean4Lean_AddInductive_instInhabitedRecInfo();
lean_mark_persistent(l_Lean4Lean_AddInductive_instInhabitedRecInfo);
l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default = _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default();
lean_mark_persistent(l_Lean4Lean_AddInductive_instInhabitedInductiveStats_default);
l_Lean4Lean_AddInductive_instInhabitedInductiveStats = _init_l_Lean4Lean_AddInductive_instInhabitedInductiveStats();
lean_mark_persistent(l_Lean4Lean_AddInductive_instInhabitedInductiveStats);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Inductive_Add(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Inductive_Add(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Inductive_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Inductive_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Inductive_Add(builtin);
}
#ifdef __cplusplus
}
#endif
