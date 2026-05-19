// Lean compiler output
// Module: Lean.Kernel.Inductive.Reduce
// Imports: public import Lean.Structure public import Lean.Util.Recognizers public import Lean.Kernel.Expr public import Lean.Environment
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParams(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getFirstIndexIdx(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isProp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_find(lean_object*, lean_object*);
lean_object* l_List_head_x3f___redArg(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_RecursorVal_getMajorInduct(lean_object*);
lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_Environment_isStructureLike(lean_object*, lean_object*);
lean_object* l_Lean_Expr_isConstructorApp_x3f_x27(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_mkNatSucc(lean_object*);
lean_object* l_Lean_RecursorVal_getMajorIdx(lean_object*);
lean_object* l_Lean_Expr_natLitToConstructor(lean_object*);
lean_object* l_Lean_Expr_strLitToConstructor(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_getFirstCtor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_mkNullaryCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_mkNullaryCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Kernel_mkNullaryCtor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_mkNullaryCtor___closed__0;
LEAN_EXPORT lean_object* l_Lean_Kernel_mkNullaryCtor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_mkNullaryCtor___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Kernel_toCtorWhenK___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Kernel_toCtorWhenK___redArg___lam__5___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_toCtorWhenK___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.Kernel.Inductive.Reduce"};
static const lean_object* l_Lean_Kernel_toCtorWhenK___redArg___closed__0 = (const lean_object*)&l_Lean_Kernel_toCtorWhenK___redArg___closed__0_value;
static const lean_string_object l_Lean_Kernel_toCtorWhenK___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Kernel.toCtorWhenK"};
static const lean_object* l_Lean_Kernel_toCtorWhenK___redArg___closed__1 = (const lean_object*)&l_Lean_Kernel_toCtorWhenK___redArg___closed__1_value;
static const lean_string_object l_Lean_Kernel_toCtorWhenK___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "assertion violation: rval.k\n  "};
static const lean_object* l_Lean_Kernel_toCtorWhenK___redArg___closed__2 = (const lean_object*)&l_Lean_Kernel_toCtorWhenK___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Kernel_toCtorWhenK___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_toCtorWhenK___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__0 = (const lean_object*)&l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__0_value;
static const lean_closure_object l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__1 = (const lean_object*)&l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__1_value;
static const lean_closure_object l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__2 = (const lean_object*)&l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__2_value;
static const lean_closure_object l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__3 = (const lean_object*)&l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__3_value;
static const lean_closure_object l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__4 = (const lean_object*)&l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__4_value;
static const lean_closure_object l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__5 = (const lean_object*)&l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__5_value;
static const lean_closure_object l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__6 = (const lean_object*)&l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__6_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Kernel.expandEtaStruct"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__0_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__1_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_expandEtaStruct(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Kernel_getRecRuleFor_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Kernel_getRecRuleFor_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_getRecRuleFor(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_getRecRuleFor___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_isOffset_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Kernel_isOffset_x3f___closed__0 = (const lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__0_value;
static const lean_string_object l_Lean_Kernel_isOffset_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "succ"};
static const lean_object* l_Lean_Kernel_isOffset_x3f___closed__1 = (const lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__1_value;
static const lean_ctor_object l_Lean_Kernel_isOffset_x3f___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Kernel_isOffset_x3f___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__2_value_aux_0),((lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__1_value),LEAN_SCALAR_PTR_LITERAL(93, 165, 73, 246, 125, 40, 156, 223)}};
static const lean_object* l_Lean_Kernel_isOffset_x3f___closed__2 = (const lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__2_value;
static const lean_string_object l_Lean_Kernel_isOffset_x3f___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "add"};
static const lean_object* l_Lean_Kernel_isOffset_x3f___closed__3 = (const lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__3_value;
static const lean_ctor_object l_Lean_Kernel_isOffset_x3f___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__0_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_Lean_Kernel_isOffset_x3f___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__4_value_aux_0),((lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__3_value),LEAN_SCALAR_PTR_LITERAL(210, 189, 86, 121, 130, 22, 242, 236)}};
static const lean_object* l_Lean_Kernel_isOffset_x3f___closed__4 = (const lean_object*)&l_Lean_Kernel_isOffset_x3f___closed__4_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_isOffset_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_isOffset_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_cleanupNatOffsetMajor(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_cleanupNatOffsetMajor___boxed(lean_object*);
static const lean_ctor_object l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_mkAppRangeChecked(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_mkAppRangeChecked___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_getFirstCtor(lean_object* v_env_1_, lean_object* v_dName_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_environment_find(v_env_1_, v_dName_2_);
if (lean_obj_tag(v___x_3_) == 1)
{
lean_object* v_val_4_; 
v_val_4_ = lean_ctor_get(v___x_3_, 0);
lean_inc(v_val_4_);
lean_dec_ref(v___x_3_);
if (lean_obj_tag(v_val_4_) == 5)
{
lean_object* v_val_5_; lean_object* v_ctors_6_; lean_object* v___x_7_; 
v_val_5_ = lean_ctor_get(v_val_4_, 0);
lean_inc_ref(v_val_5_);
lean_dec_ref(v_val_4_);
v_ctors_6_ = lean_ctor_get(v_val_5_, 4);
lean_inc(v_ctors_6_);
lean_dec_ref(v_val_5_);
v___x_7_ = l_List_head_x3f___redArg(v_ctors_6_);
lean_dec(v_ctors_6_);
return v___x_7_;
}
else
{
lean_object* v___x_8_; 
lean_dec(v_val_4_);
v___x_8_ = lean_box(0);
return v___x_8_;
}
}
else
{
lean_object* v___x_9_; 
lean_dec(v___x_3_);
v___x_9_ = lean_box(0);
return v___x_9_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_mkNullaryCtor_spec__0(lean_object* v_env_10_, lean_object* v_nparams_11_, lean_object* v_x_12_, lean_object* v_x_13_, lean_object* v_x_14_){
_start:
{
if (lean_obj_tag(v_x_12_) == 5)
{
lean_object* v_fn_15_; lean_object* v_arg_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
v_fn_15_ = lean_ctor_get(v_x_12_, 0);
lean_inc_ref(v_fn_15_);
v_arg_16_ = lean_ctor_get(v_x_12_, 1);
lean_inc_ref(v_arg_16_);
lean_dec_ref(v_x_12_);
v___x_17_ = lean_array_set(v_x_13_, v_x_14_, v_arg_16_);
v___x_18_ = lean_unsigned_to_nat(1u);
v___x_19_ = lean_nat_sub(v_x_14_, v___x_18_);
lean_dec(v_x_14_);
v_x_12_ = v_fn_15_;
v_x_13_ = v___x_17_;
v_x_14_ = v___x_19_;
goto _start;
}
else
{
lean_dec(v_x_14_);
if (lean_obj_tag(v_x_12_) == 4)
{
lean_object* v_declName_21_; lean_object* v_us_22_; lean_object* v___x_23_; 
v_declName_21_ = lean_ctor_get(v_x_12_, 0);
lean_inc(v_declName_21_);
v_us_22_ = lean_ctor_get(v_x_12_, 1);
lean_inc(v_us_22_);
lean_dec_ref(v_x_12_);
v___x_23_ = l_Lean_Kernel_getFirstCtor(v_env_10_, v_declName_21_);
if (lean_obj_tag(v___x_23_) == 0)
{
lean_object* v___x_24_; 
lean_dec(v_us_22_);
lean_dec_ref(v_x_13_);
v___x_24_ = lean_box(0);
return v___x_24_;
}
else
{
lean_object* v_val_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_35_; 
v_val_25_ = lean_ctor_get(v___x_23_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_23_);
if (v_isSharedCheck_35_ == 0)
{
v___x_27_ = v___x_23_;
v_isShared_28_ = v_isSharedCheck_35_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_val_25_);
lean_dec(v___x_23_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_35_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_29_ = l_Lean_Expr_const___override(v_val_25_, v_us_22_);
v___x_30_ = lean_unsigned_to_nat(0u);
v___x_31_ = l_Lean_mkAppRange(v___x_29_, v___x_30_, v_nparams_11_, v_x_13_);
lean_dec_ref(v_x_13_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 0, v___x_31_);
v___x_33_ = v___x_27_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
else
{
lean_object* v___x_36_; 
lean_dec_ref(v_x_13_);
lean_dec_ref(v_x_12_);
lean_dec_ref(v_env_10_);
v___x_36_ = lean_box(0);
return v___x_36_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_mkNullaryCtor_spec__0___boxed(lean_object* v_env_37_, lean_object* v_nparams_38_, lean_object* v_x_39_, lean_object* v_x_40_, lean_object* v_x_41_){
_start:
{
lean_object* v_res_42_; 
v_res_42_ = l_Lean_Expr_withAppAux___at___00Lean_Kernel_mkNullaryCtor_spec__0(v_env_37_, v_nparams_38_, v_x_39_, v_x_40_, v_x_41_);
lean_dec(v_nparams_38_);
return v_res_42_;
}
}
static lean_object* _init_l_Lean_Kernel_mkNullaryCtor___closed__0(void){
_start:
{
lean_object* v___x_43_; lean_object* v_dummy_44_; 
v___x_43_ = lean_box(0);
v_dummy_44_ = l_Lean_Expr_sort___override(v___x_43_);
return v_dummy_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_mkNullaryCtor(lean_object* v_env_45_, lean_object* v_type_46_, lean_object* v_nparams_47_){
_start:
{
lean_object* v_dummy_48_; lean_object* v_nargs_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; lean_object* v___x_53_; 
v_dummy_48_ = lean_obj_once(&l_Lean_Kernel_mkNullaryCtor___closed__0, &l_Lean_Kernel_mkNullaryCtor___closed__0_once, _init_l_Lean_Kernel_mkNullaryCtor___closed__0);
v_nargs_49_ = l_Lean_Expr_getAppNumArgs(v_type_46_);
lean_inc(v_nargs_49_);
v___x_50_ = lean_mk_array(v_nargs_49_, v_dummy_48_);
v___x_51_ = lean_unsigned_to_nat(1u);
v___x_52_ = lean_nat_sub(v_nargs_49_, v___x_51_);
lean_dec(v_nargs_49_);
v___x_53_ = l_Lean_Expr_withAppAux___at___00Lean_Kernel_mkNullaryCtor_spec__0(v_env_45_, v_nparams_47_, v_type_46_, v___x_50_, v___x_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_mkNullaryCtor___boxed(lean_object* v_env_54_, lean_object* v_type_55_, lean_object* v_nparams_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_Kernel_mkNullaryCtor(v_env_54_, v_type_55_, v_nparams_56_);
lean_dec(v_nparams_56_);
return v_res_57_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__0(lean_object* v_toApplicative_58_, lean_object* v_e_59_, lean_object* v_val_60_, uint8_t v_____do__lift_61_){
_start:
{
if (v_____do__lift_61_ == 0)
{
lean_object* v_toPure_62_; lean_object* v___x_63_; 
lean_dec_ref(v_val_60_);
v_toPure_62_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_62_);
lean_dec_ref(v_toApplicative_58_);
v___x_63_ = lean_apply_2(v_toPure_62_, lean_box(0), v_e_59_);
return v___x_63_;
}
else
{
lean_object* v_toPure_64_; lean_object* v___x_65_; 
lean_dec_ref(v_e_59_);
v_toPure_64_ = lean_ctor_get(v_toApplicative_58_, 1);
lean_inc(v_toPure_64_);
lean_dec_ref(v_toApplicative_58_);
v___x_65_ = lean_apply_2(v_toPure_64_, lean_box(0), v_val_60_);
return v___x_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__0___boxed(lean_object* v_toApplicative_66_, lean_object* v_e_67_, lean_object* v_val_68_, lean_object* v_____do__lift_69_){
_start:
{
uint8_t v_____do__lift_1209__boxed_70_; lean_object* v_res_71_; 
v_____do__lift_1209__boxed_70_ = lean_unbox(v_____do__lift_69_);
v_res_71_ = l_Lean_Kernel_toCtorWhenK___redArg___lam__0(v_toApplicative_66_, v_e_67_, v_val_68_, v_____do__lift_1209__boxed_70_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__1(lean_object* v_isDefEq_72_, lean_object* v_appType_73_, lean_object* v_toBind_74_, lean_object* v___f_75_, lean_object* v_____do__lift_76_){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = lean_apply_2(v_isDefEq_72_, v_appType_73_, v_____do__lift_76_);
v___x_78_ = lean_apply_4(v_toBind_74_, lean_box(0), lean_box(0), v___x_77_, v___f_75_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__2(lean_object* v_env_79_, lean_object* v_appType_80_, lean_object* v_numParams_81_, lean_object* v_toApplicative_82_, lean_object* v_e_83_, lean_object* v_isDefEq_84_, lean_object* v_toBind_85_, lean_object* v_inferType_86_, lean_object* v_____r_87_){
_start:
{
lean_object* v___x_88_; 
lean_inc_ref(v_appType_80_);
v___x_88_ = l_Lean_Kernel_mkNullaryCtor(v_env_79_, v_appType_80_, v_numParams_81_);
if (lean_obj_tag(v___x_88_) == 1)
{
lean_object* v_val_89_; lean_object* v___f_90_; lean_object* v___f_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_val_89_ = lean_ctor_get(v___x_88_, 0);
lean_inc_n(v_val_89_, 2);
lean_dec_ref(v___x_88_);
v___f_90_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_90_, 0, v_toApplicative_82_);
lean_closure_set(v___f_90_, 1, v_e_83_);
lean_closure_set(v___f_90_, 2, v_val_89_);
lean_inc(v_toBind_85_);
v___f_91_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__1), 5, 4);
lean_closure_set(v___f_91_, 0, v_isDefEq_84_);
lean_closure_set(v___f_91_, 1, v_appType_80_);
lean_closure_set(v___f_91_, 2, v_toBind_85_);
lean_closure_set(v___f_91_, 3, v___f_90_);
v___x_92_ = lean_apply_1(v_inferType_86_, v_val_89_);
v___x_93_ = lean_apply_4(v_toBind_85_, lean_box(0), lean_box(0), v___x_92_, v___f_91_);
return v___x_93_;
}
else
{
lean_object* v_toPure_94_; lean_object* v___x_95_; 
lean_dec(v___x_88_);
lean_dec(v_inferType_86_);
lean_dec(v_toBind_85_);
lean_dec(v_isDefEq_84_);
lean_dec_ref(v_appType_80_);
v_toPure_94_ = lean_ctor_get(v_toApplicative_82_, 1);
lean_inc(v_toPure_94_);
lean_dec_ref(v_toApplicative_82_);
v___x_95_ = lean_apply_2(v_toPure_94_, lean_box(0), v_e_83_);
return v___x_95_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__2___boxed(lean_object* v_env_96_, lean_object* v_appType_97_, lean_object* v_numParams_98_, lean_object* v_toApplicative_99_, lean_object* v_e_100_, lean_object* v_isDefEq_101_, lean_object* v_toBind_102_, lean_object* v_inferType_103_, lean_object* v_____r_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Kernel_toCtorWhenK___redArg___lam__2(v_env_96_, v_appType_97_, v_numParams_98_, v_toApplicative_99_, v_e_100_, v_isDefEq_101_, v_toBind_102_, v_inferType_103_, v_____r_104_);
lean_dec(v_numParams_98_);
return v_res_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__3(lean_object* v___f_106_, lean_object* v___x_107_, lean_object* v_toApplicative_108_, lean_object* v_____s_109_){
_start:
{
lean_object* v_fst_110_; 
v_fst_110_ = lean_ctor_get(v_____s_109_, 0);
lean_inc(v_fst_110_);
lean_dec_ref(v_____s_109_);
if (lean_obj_tag(v_fst_110_) == 0)
{
lean_object* v___x_111_; 
lean_dec_ref(v_toApplicative_108_);
v___x_111_ = lean_apply_1(v___f_106_, v___x_107_);
return v___x_111_;
}
else
{
lean_object* v_val_112_; lean_object* v_toPure_113_; lean_object* v___x_114_; 
lean_dec(v___f_106_);
v_val_112_ = lean_ctor_get(v_fst_110_, 0);
lean_inc(v_val_112_);
lean_dec_ref(v_fst_110_);
v_toPure_113_ = lean_ctor_get(v_toApplicative_108_, 1);
lean_inc(v_toPure_113_);
lean_dec_ref(v_toApplicative_108_);
v___x_114_ = lean_apply_2(v_toPure_113_, lean_box(0), v_val_112_);
return v___x_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__4(lean_object* v_appTypeArgs_115_, lean_object* v_toApplicative_116_, lean_object* v___x_117_, lean_object* v_e_118_, lean_object* v___x_119_, lean_object* v_i_120_, lean_object* v_h_121_, lean_object* v_____s_122_){
_start:
{
lean_object* v___x_123_; uint8_t v___x_124_; 
v___x_123_ = lean_array_fget_borrowed(v_appTypeArgs_115_, v_i_120_);
v___x_124_ = l_Lean_Expr_hasExprMVar(v___x_123_);
if (v___x_124_ == 0)
{
lean_object* v_toPure_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
lean_dec_ref(v_e_118_);
v_toPure_125_ = lean_ctor_get(v_toApplicative_116_, 1);
lean_inc(v_toPure_125_);
lean_dec_ref(v_toApplicative_116_);
v___x_126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_126_, 0, v___x_117_);
v___x_127_ = lean_apply_2(v_toPure_125_, lean_box(0), v___x_126_);
return v___x_127_;
}
else
{
lean_object* v_toPure_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec_ref(v___x_117_);
v_toPure_128_ = lean_ctor_get(v_toApplicative_116_, 1);
lean_inc(v_toPure_128_);
lean_dec_ref(v_toApplicative_116_);
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_e_118_);
v___x_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
lean_ctor_set(v___x_130_, 1, v___x_119_);
v___x_131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
v___x_132_ = lean_apply_2(v_toPure_128_, lean_box(0), v___x_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__4___boxed(lean_object* v_appTypeArgs_133_, lean_object* v_toApplicative_134_, lean_object* v___x_135_, lean_object* v_e_136_, lean_object* v___x_137_, lean_object* v_i_138_, lean_object* v_h_139_, lean_object* v_____s_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_Kernel_toCtorWhenK___redArg___lam__4(v_appTypeArgs_133_, v_toApplicative_134_, v___x_135_, v_e_136_, v___x_137_, v_i_138_, v_h_139_, v_____s_140_);
lean_dec_ref(v_____s_140_);
lean_dec(v_i_138_);
lean_dec_ref(v_appTypeArgs_133_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__5(lean_object* v_rval_145_, lean_object* v_toApplicative_146_, lean_object* v_e_147_, lean_object* v_env_148_, lean_object* v_numParams_149_, lean_object* v_isDefEq_150_, lean_object* v_toBind_151_, lean_object* v_inferType_152_, lean_object* v_inst_153_, lean_object* v_appType_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_Expr_getAppFn(v_appType_154_);
if (lean_obj_tag(v___x_155_) == 4)
{
lean_object* v_declName_156_; lean_object* v___x_157_; uint8_t v___x_158_; 
v_declName_156_ = lean_ctor_get(v___x_155_, 0);
lean_inc(v_declName_156_);
lean_dec_ref(v___x_155_);
v___x_157_ = l_Lean_RecursorVal_getMajorInduct(v_rval_145_);
v___x_158_ = lean_name_eq(v_declName_156_, v___x_157_);
lean_dec(v___x_157_);
lean_dec(v_declName_156_);
if (v___x_158_ == 0)
{
lean_object* v_toPure_159_; lean_object* v___x_160_; 
lean_dec_ref(v_appType_154_);
lean_dec_ref(v_inst_153_);
lean_dec(v_inferType_152_);
lean_dec(v_toBind_151_);
lean_dec(v_isDefEq_150_);
lean_dec(v_numParams_149_);
lean_dec_ref(v_env_148_);
v_toPure_159_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_inc(v_toPure_159_);
lean_dec_ref(v_toApplicative_146_);
v___x_160_ = lean_apply_2(v_toPure_159_, lean_box(0), v_e_147_);
return v___x_160_;
}
else
{
lean_object* v___f_161_; uint8_t v___x_162_; 
lean_inc(v_inferType_152_);
lean_inc(v_toBind_151_);
lean_inc(v_isDefEq_150_);
lean_inc_ref(v_e_147_);
lean_inc_ref(v_toApplicative_146_);
lean_inc(v_numParams_149_);
lean_inc_ref(v_appType_154_);
lean_inc_ref(v_env_148_);
v___f_161_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__2___boxed), 9, 8);
lean_closure_set(v___f_161_, 0, v_env_148_);
lean_closure_set(v___f_161_, 1, v_appType_154_);
lean_closure_set(v___f_161_, 2, v_numParams_149_);
lean_closure_set(v___f_161_, 3, v_toApplicative_146_);
lean_closure_set(v___f_161_, 4, v_e_147_);
lean_closure_set(v___f_161_, 5, v_isDefEq_150_);
lean_closure_set(v___f_161_, 6, v_toBind_151_);
lean_closure_set(v___f_161_, 7, v_inferType_152_);
v___x_162_ = l_Lean_Expr_hasExprMVar(v_appType_154_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
lean_dec_ref(v___f_161_);
lean_dec_ref(v_inst_153_);
v___x_163_ = lean_box(0);
v___x_164_ = l_Lean_Kernel_toCtorWhenK___redArg___lam__2(v_env_148_, v_appType_154_, v_numParams_149_, v_toApplicative_146_, v_e_147_, v_isDefEq_150_, v_toBind_151_, v_inferType_152_, v___x_163_);
lean_dec(v_numParams_149_);
return v___x_164_;
}
else
{
lean_object* v_dummy_165_; lean_object* v_nargs_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v_appTypeArgs_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
lean_dec(v_inferType_152_);
lean_dec(v_isDefEq_150_);
lean_dec_ref(v_env_148_);
v_dummy_165_ = lean_obj_once(&l_Lean_Kernel_mkNullaryCtor___closed__0, &l_Lean_Kernel_mkNullaryCtor___closed__0_once, _init_l_Lean_Kernel_mkNullaryCtor___closed__0);
v_nargs_166_ = l_Lean_Expr_getAppNumArgs(v_appType_154_);
lean_inc(v_nargs_166_);
v___x_167_ = lean_mk_array(v_nargs_166_, v_dummy_165_);
v___x_168_ = lean_unsigned_to_nat(1u);
v___x_169_ = lean_nat_sub(v_nargs_166_, v___x_168_);
lean_dec(v_nargs_166_);
v_appTypeArgs_170_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_appType_154_, v___x_167_, v___x_169_);
v___x_171_ = lean_array_get_size(v_appTypeArgs_170_);
lean_inc(v_numParams_149_);
v___x_172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_172_, 0, v_numParams_149_);
lean_ctor_set(v___x_172_, 1, v___x_171_);
lean_ctor_set(v___x_172_, 2, v___x_168_);
v___x_173_ = lean_box(0);
lean_inc_ref(v_toApplicative_146_);
v___f_174_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__3), 4, 3);
lean_closure_set(v___f_174_, 0, v___f_161_);
lean_closure_set(v___f_174_, 1, v___x_173_);
lean_closure_set(v___f_174_, 2, v_toApplicative_146_);
v___x_175_ = ((lean_object*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__5___closed__0));
v___f_176_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__4___boxed), 8, 5);
lean_closure_set(v___f_176_, 0, v_appTypeArgs_170_);
lean_closure_set(v___f_176_, 1, v_toApplicative_146_);
lean_closure_set(v___f_176_, 2, v___x_175_);
lean_closure_set(v___f_176_, 3, v_e_147_);
lean_closure_set(v___f_176_, 4, v___x_173_);
v___x_177_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop(lean_box(0), lean_box(0), v_inst_153_, v___x_172_, v___f_176_, v___x_175_, v_numParams_149_, lean_box(0), lean_box(0));
v___x_178_ = lean_apply_4(v_toBind_151_, lean_box(0), lean_box(0), v___x_177_, v___f_174_);
return v___x_178_;
}
}
}
else
{
lean_object* v_toPure_179_; lean_object* v___x_180_; 
lean_dec_ref(v___x_155_);
lean_dec_ref(v_appType_154_);
lean_dec_ref(v_inst_153_);
lean_dec(v_inferType_152_);
lean_dec(v_toBind_151_);
lean_dec(v_isDefEq_150_);
lean_dec(v_numParams_149_);
lean_dec_ref(v_env_148_);
lean_dec_ref(v_rval_145_);
v_toPure_179_ = lean_ctor_get(v_toApplicative_146_, 1);
lean_inc(v_toPure_179_);
lean_dec_ref(v_toApplicative_146_);
v___x_180_ = lean_apply_2(v_toPure_179_, lean_box(0), v_e_147_);
return v___x_180_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg___lam__6(lean_object* v_whnf_181_, lean_object* v_toBind_182_, lean_object* v___f_183_, lean_object* v_____do__lift_184_){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = lean_apply_1(v_whnf_181_, v_____do__lift_184_);
v___x_186_ = lean_apply_4(v_toBind_182_, lean_box(0), lean_box(0), v___x_185_, v___f_183_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Kernel_toCtorWhenK___redArg___closed__3(void){
_start:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_190_ = ((lean_object*)(l_Lean_Kernel_toCtorWhenK___redArg___closed__2));
v___x_191_ = lean_unsigned_to_nat(2u);
v___x_192_ = lean_unsigned_to_nat(31u);
v___x_193_ = ((lean_object*)(l_Lean_Kernel_toCtorWhenK___redArg___closed__1));
v___x_194_ = ((lean_object*)(l_Lean_Kernel_toCtorWhenK___redArg___closed__0));
v___x_195_ = l_mkPanicMessageWithDecl(v___x_194_, v___x_193_, v___x_192_, v___x_191_, v___x_190_);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK___redArg(lean_object* v_inst_196_, lean_object* v_env_197_, lean_object* v_whnf_198_, lean_object* v_inferType_199_, lean_object* v_isDefEq_200_, lean_object* v_rval_201_, lean_object* v_e_202_){
_start:
{
uint8_t v_k_203_; 
v_k_203_ = lean_ctor_get_uint8(v_rval_201_, sizeof(void*)*7);
if (v_k_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; 
lean_dec_ref(v_e_202_);
lean_dec_ref(v_rval_201_);
lean_dec(v_isDefEq_200_);
lean_dec(v_inferType_199_);
lean_dec(v_whnf_198_);
lean_dec_ref(v_env_197_);
v___x_204_ = l_Lean_instInhabitedExpr;
v___x_205_ = l_instInhabitedOfMonad___redArg(v_inst_196_, v___x_204_);
v___x_206_ = lean_obj_once(&l_Lean_Kernel_toCtorWhenK___redArg___closed__3, &l_Lean_Kernel_toCtorWhenK___redArg___closed__3_once, _init_l_Lean_Kernel_toCtorWhenK___redArg___closed__3);
v___x_207_ = l_panic___redArg(v___x_205_, v___x_206_);
lean_dec(v___x_205_);
return v___x_207_;
}
else
{
lean_object* v_numParams_208_; lean_object* v_toApplicative_209_; lean_object* v_toBind_210_; lean_object* v___f_211_; lean_object* v___f_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_numParams_208_ = lean_ctor_get(v_rval_201_, 2);
lean_inc(v_numParams_208_);
v_toApplicative_209_ = lean_ctor_get(v_inst_196_, 0);
lean_inc_ref(v_toApplicative_209_);
v_toBind_210_ = lean_ctor_get(v_inst_196_, 1);
lean_inc_n(v_toBind_210_, 3);
lean_inc(v_inferType_199_);
lean_inc_ref(v_e_202_);
v___f_211_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__5), 10, 9);
lean_closure_set(v___f_211_, 0, v_rval_201_);
lean_closure_set(v___f_211_, 1, v_toApplicative_209_);
lean_closure_set(v___f_211_, 2, v_e_202_);
lean_closure_set(v___f_211_, 3, v_env_197_);
lean_closure_set(v___f_211_, 4, v_numParams_208_);
lean_closure_set(v___f_211_, 5, v_isDefEq_200_);
lean_closure_set(v___f_211_, 6, v_toBind_210_);
lean_closure_set(v___f_211_, 7, v_inferType_199_);
lean_closure_set(v___f_211_, 8, v_inst_196_);
v___f_212_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__6), 4, 3);
lean_closure_set(v___f_212_, 0, v_whnf_198_);
lean_closure_set(v___f_212_, 1, v_toBind_210_);
lean_closure_set(v___f_212_, 2, v___f_211_);
v___x_213_ = lean_apply_1(v_inferType_199_, v_e_202_);
v___x_214_ = lean_apply_4(v_toBind_210_, lean_box(0), lean_box(0), v___x_213_, v___f_212_);
return v___x_214_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenK(lean_object* v_m_215_, lean_object* v_inst_216_, lean_object* v_env_217_, lean_object* v_whnf_218_, lean_object* v_inferType_219_, lean_object* v_isDefEq_220_, lean_object* v_rval_221_, lean_object* v_e_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Kernel_toCtorWhenK___redArg(v_inst_216_, v_env_217_, v_whnf_218_, v_inferType_219_, v_isDefEq_220_, v_rval_221_, v_e_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0(lean_object* v_msg_231_){
_start:
{
lean_object* v___f_232_; lean_object* v___f_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___f_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___f_232_ = ((lean_object*)(l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__0));
v___f_233_ = ((lean_object*)(l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__1));
v___f_234_ = ((lean_object*)(l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__2));
v___f_235_ = ((lean_object*)(l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__3));
v___f_236_ = ((lean_object*)(l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__4));
v___f_237_ = ((lean_object*)(l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__5));
v___f_238_ = ((lean_object*)(l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0___closed__6));
v___x_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_239_, 0, v___f_232_);
lean_ctor_set(v___x_239_, 1, v___f_233_);
v___x_240_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
lean_ctor_set(v___x_240_, 1, v___f_234_);
lean_ctor_set(v___x_240_, 2, v___f_235_);
lean_ctor_set(v___x_240_, 3, v___f_236_);
lean_ctor_set(v___x_240_, 4, v___f_237_);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___f_238_);
v___x_242_ = l_Lean_instInhabitedExpr;
v___x_243_ = l_instInhabitedOfMonad___redArg(v___x_241_, v___x_242_);
v___x_244_ = lean_panic_fn_borrowed(v___x_243_, v_msg_231_);
lean_dec(v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg(lean_object* v_declName_245_, lean_object* v_e_246_, lean_object* v_range_247_, lean_object* v_b_248_, lean_object* v_i_249_){
_start:
{
lean_object* v_stop_250_; lean_object* v_step_251_; uint8_t v___x_252_; 
v_stop_250_ = lean_ctor_get(v_range_247_, 1);
v_step_251_ = lean_ctor_get(v_range_247_, 2);
v___x_252_ = lean_nat_dec_lt(v_i_249_, v_stop_250_);
if (v___x_252_ == 0)
{
lean_dec(v_i_249_);
lean_dec_ref(v_e_246_);
lean_dec(v_declName_245_);
return v_b_248_;
}
else
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
lean_inc_ref(v_e_246_);
lean_inc(v_i_249_);
lean_inc(v_declName_245_);
v___x_253_ = l_Lean_Expr_proj___override(v_declName_245_, v_i_249_, v_e_246_);
v___x_254_ = l_Lean_Expr_app___override(v_b_248_, v___x_253_);
v___x_255_ = lean_nat_add(v_i_249_, v_step_251_);
lean_dec(v_i_249_);
v_b_248_ = v___x_254_;
v_i_249_ = v___x_255_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg___boxed(lean_object* v_declName_257_, lean_object* v_e_258_, lean_object* v_range_259_, lean_object* v_b_260_, lean_object* v_i_261_){
_start:
{
lean_object* v_res_262_; 
v_res_262_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg(v_declName_257_, v_e_258_, v_range_259_, v_b_260_, v_i_261_);
lean_dec_ref(v_range_259_);
return v_res_262_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_265_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__1));
v___x_266_ = lean_unsigned_to_nat(48u);
v___x_267_ = lean_unsigned_to_nat(47u);
v___x_268_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__0));
v___x_269_ = ((lean_object*)(l_Lean_Kernel_toCtorWhenK___redArg___closed__0));
v___x_270_ = l_mkPanicMessageWithDecl(v___x_269_, v___x_268_, v___x_267_, v___x_266_, v___x_265_);
return v___x_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2(lean_object* v_env_271_, lean_object* v_e_272_, lean_object* v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_273_) == 5)
{
lean_object* v_fn_279_; lean_object* v_arg_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
v_fn_279_ = lean_ctor_get(v_x_273_, 0);
lean_inc_ref(v_fn_279_);
v_arg_280_ = lean_ctor_get(v_x_273_, 1);
lean_inc_ref(v_arg_280_);
lean_dec_ref(v_x_273_);
v___x_281_ = lean_array_set(v_x_274_, v_x_275_, v_arg_280_);
v___x_282_ = lean_unsigned_to_nat(1u);
v___x_283_ = lean_nat_sub(v_x_275_, v___x_282_);
lean_dec(v_x_275_);
v_x_273_ = v_fn_279_;
v_x_274_ = v___x_281_;
v_x_275_ = v___x_283_;
goto _start;
}
else
{
lean_dec(v_x_275_);
if (lean_obj_tag(v_x_273_) == 4)
{
lean_object* v_declName_285_; lean_object* v_us_286_; lean_object* v___x_287_; 
v_declName_285_ = lean_ctor_get(v_x_273_, 0);
lean_inc_n(v_declName_285_, 2);
v_us_286_ = lean_ctor_get(v_x_273_, 1);
lean_inc(v_us_286_);
lean_dec_ref(v_x_273_);
lean_inc_ref(v_env_271_);
v___x_287_ = l_Lean_Kernel_getFirstCtor(v_env_271_, v_declName_285_);
if (lean_obj_tag(v___x_287_) == 1)
{
lean_object* v_val_288_; lean_object* v___x_289_; 
v_val_288_ = lean_ctor_get(v___x_287_, 0);
lean_inc_n(v_val_288_, 2);
lean_dec_ref(v___x_287_);
v___x_289_ = lean_environment_find(v_env_271_, v_val_288_);
if (lean_obj_tag(v___x_289_) == 1)
{
lean_object* v_val_290_; 
v_val_290_ = lean_ctor_get(v___x_289_, 0);
lean_inc(v_val_290_);
lean_dec_ref(v___x_289_);
if (lean_obj_tag(v_val_290_) == 6)
{
lean_object* v_val_291_; lean_object* v_numParams_292_; lean_object* v_numFields_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v_result_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_val_291_ = lean_ctor_get(v_val_290_, 0);
lean_inc_ref(v_val_291_);
lean_dec_ref(v_val_290_);
v_numParams_292_ = lean_ctor_get(v_val_291_, 3);
lean_inc(v_numParams_292_);
v_numFields_293_ = lean_ctor_get(v_val_291_, 4);
lean_inc(v_numFields_293_);
lean_dec_ref(v_val_291_);
v___x_294_ = l_Lean_Expr_const___override(v_val_288_, v_us_286_);
v___x_295_ = lean_unsigned_to_nat(0u);
v_result_296_ = l_Lean_mkAppRange(v___x_294_, v___x_295_, v_numParams_292_, v_x_274_);
lean_dec_ref(v_x_274_);
lean_dec(v_numParams_292_);
v___x_297_ = lean_unsigned_to_nat(1u);
v___x_298_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_298_, 0, v___x_295_);
lean_ctor_set(v___x_298_, 1, v_numFields_293_);
lean_ctor_set(v___x_298_, 2, v___x_297_);
v___x_299_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg(v_declName_285_, v_e_272_, v___x_298_, v_result_296_, v___x_295_);
lean_dec_ref(v___x_298_);
return v___x_299_;
}
else
{
lean_dec(v_val_290_);
lean_dec(v_val_288_);
lean_dec(v_us_286_);
lean_dec(v_declName_285_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_e_272_);
goto v___jp_276_;
}
}
else
{
lean_dec(v___x_289_);
lean_dec(v_val_288_);
lean_dec(v_us_286_);
lean_dec(v_declName_285_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_e_272_);
goto v___jp_276_;
}
}
else
{
lean_dec(v___x_287_);
lean_dec(v_us_286_);
lean_dec(v_declName_285_);
lean_dec_ref(v_x_274_);
lean_dec_ref(v_env_271_);
return v_e_272_;
}
}
else
{
lean_dec_ref(v_x_274_);
lean_dec_ref(v_x_273_);
lean_dec_ref(v_env_271_);
return v_e_272_;
}
}
v___jp_276_:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2);
v___x_278_ = l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0(v___x_277_);
return v___x_278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2(lean_object* v_e_300_, lean_object* v_env_301_, lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
if (lean_obj_tag(v_x_302_) == 5)
{
lean_object* v_fn_308_; lean_object* v_arg_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; 
v_fn_308_ = lean_ctor_get(v_x_302_, 0);
lean_inc_ref(v_fn_308_);
v_arg_309_ = lean_ctor_get(v_x_302_, 1);
lean_inc_ref(v_arg_309_);
lean_dec_ref(v_x_302_);
v___x_310_ = lean_array_set(v_x_303_, v_x_304_, v_arg_309_);
v___x_311_ = lean_unsigned_to_nat(1u);
v___x_312_ = lean_nat_sub(v_x_304_, v___x_311_);
v___x_313_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2(v_env_301_, v_e_300_, v_fn_308_, v___x_310_, v___x_312_);
return v___x_313_;
}
else
{
if (lean_obj_tag(v_x_302_) == 4)
{
lean_object* v_declName_314_; lean_object* v_us_315_; lean_object* v___x_316_; 
v_declName_314_ = lean_ctor_get(v_x_302_, 0);
lean_inc_n(v_declName_314_, 2);
v_us_315_ = lean_ctor_get(v_x_302_, 1);
lean_inc(v_us_315_);
lean_dec_ref(v_x_302_);
lean_inc_ref(v_env_301_);
v___x_316_ = l_Lean_Kernel_getFirstCtor(v_env_301_, v_declName_314_);
if (lean_obj_tag(v___x_316_) == 1)
{
lean_object* v_val_317_; lean_object* v___x_318_; 
v_val_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc_n(v_val_317_, 2);
lean_dec_ref(v___x_316_);
v___x_318_ = lean_environment_find(v_env_301_, v_val_317_);
if (lean_obj_tag(v___x_318_) == 1)
{
lean_object* v_val_319_; 
v_val_319_ = lean_ctor_get(v___x_318_, 0);
lean_inc(v_val_319_);
lean_dec_ref(v___x_318_);
if (lean_obj_tag(v_val_319_) == 6)
{
lean_object* v_val_320_; lean_object* v_numParams_321_; lean_object* v_numFields_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v_result_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; 
v_val_320_ = lean_ctor_get(v_val_319_, 0);
lean_inc_ref(v_val_320_);
lean_dec_ref(v_val_319_);
v_numParams_321_ = lean_ctor_get(v_val_320_, 3);
lean_inc(v_numParams_321_);
v_numFields_322_ = lean_ctor_get(v_val_320_, 4);
lean_inc(v_numFields_322_);
lean_dec_ref(v_val_320_);
v___x_323_ = l_Lean_Expr_const___override(v_val_317_, v_us_315_);
v___x_324_ = lean_unsigned_to_nat(0u);
v_result_325_ = l_Lean_mkAppRange(v___x_323_, v___x_324_, v_numParams_321_, v_x_303_);
lean_dec_ref(v_x_303_);
lean_dec(v_numParams_321_);
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_327_, 0, v___x_324_);
lean_ctor_set(v___x_327_, 1, v_numFields_322_);
lean_ctor_set(v___x_327_, 2, v___x_326_);
v___x_328_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg(v_declName_314_, v_e_300_, v___x_327_, v_result_325_, v___x_324_);
lean_dec_ref(v___x_327_);
return v___x_328_;
}
else
{
lean_dec(v_val_319_);
lean_dec(v_val_317_);
lean_dec(v_us_315_);
lean_dec(v_declName_314_);
lean_dec_ref(v_x_303_);
lean_dec_ref(v_e_300_);
goto v___jp_305_;
}
}
else
{
lean_dec(v___x_318_);
lean_dec(v_val_317_);
lean_dec(v_us_315_);
lean_dec(v_declName_314_);
lean_dec_ref(v_x_303_);
lean_dec_ref(v_e_300_);
goto v___jp_305_;
}
}
else
{
lean_dec(v___x_316_);
lean_dec(v_us_315_);
lean_dec(v_declName_314_);
lean_dec_ref(v_x_303_);
lean_dec_ref(v_env_301_);
return v_e_300_;
}
}
else
{
lean_dec_ref(v_x_303_);
lean_dec_ref(v_x_302_);
lean_dec_ref(v_env_301_);
return v_e_300_;
}
}
v___jp_305_:
{
lean_object* v___x_306_; lean_object* v___x_307_; 
v___x_306_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2_spec__2___closed__2);
v___x_307_ = l_panic___at___00Lean_Kernel_expandEtaStruct_spec__0(v___x_306_);
return v___x_307_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2___boxed(lean_object* v_e_329_, lean_object* v_env_330_, lean_object* v_x_331_, lean_object* v_x_332_, lean_object* v_x_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2(v_e_329_, v_env_330_, v_x_331_, v_x_332_, v_x_333_);
lean_dec(v_x_333_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_expandEtaStruct(lean_object* v_env_335_, lean_object* v_eType_336_, lean_object* v_e_337_){
_start:
{
lean_object* v_dummy_338_; lean_object* v_nargs_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
v_dummy_338_ = lean_obj_once(&l_Lean_Kernel_mkNullaryCtor___closed__0, &l_Lean_Kernel_mkNullaryCtor___closed__0_once, _init_l_Lean_Kernel_mkNullaryCtor___closed__0);
v_nargs_339_ = l_Lean_Expr_getAppNumArgs(v_eType_336_);
lean_inc(v_nargs_339_);
v___x_340_ = lean_mk_array(v_nargs_339_, v_dummy_338_);
v___x_341_ = lean_unsigned_to_nat(1u);
v___x_342_ = lean_nat_sub(v_nargs_339_, v___x_341_);
lean_dec(v_nargs_339_);
v___x_343_ = l_Lean_Expr_withAppAux___at___00Lean_Kernel_expandEtaStruct_spec__2(v_e_337_, v_env_335_, v_eType_336_, v___x_340_, v___x_342_);
lean_dec(v___x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1(lean_object* v_declName_344_, lean_object* v_e_345_, lean_object* v_range_346_, lean_object* v_b_347_, lean_object* v_i_348_, lean_object* v_hs_349_, lean_object* v_hl_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___redArg(v_declName_344_, v_e_345_, v_range_346_, v_b_347_, v_i_348_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1___boxed(lean_object* v_declName_352_, lean_object* v_e_353_, lean_object* v_range_354_, lean_object* v_b_355_, lean_object* v_i_356_, lean_object* v_hs_357_, lean_object* v_hl_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_expandEtaStruct_spec__1(v_declName_352_, v_e_353_, v_range_354_, v_b_355_, v_i_356_, v_hs_357_, v_hl_358_);
lean_dec_ref(v_range_354_);
return v_res_359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__0(lean_object* v_toApplicative_360_, lean_object* v_env_361_, lean_object* v_eType_362_, lean_object* v_e_363_, lean_object* v_____do__lift_364_){
_start:
{
uint8_t v___x_365_; 
v___x_365_ = l_Lean_Expr_isProp(v_____do__lift_364_);
if (v___x_365_ == 0)
{
lean_object* v_toPure_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v_toPure_366_ = lean_ctor_get(v_toApplicative_360_, 1);
lean_inc(v_toPure_366_);
lean_dec_ref(v_toApplicative_360_);
v___x_367_ = l_Lean_Kernel_expandEtaStruct(v_env_361_, v_eType_362_, v_e_363_);
v___x_368_ = lean_apply_2(v_toPure_366_, lean_box(0), v___x_367_);
return v___x_368_;
}
else
{
lean_object* v_toPure_369_; lean_object* v___x_370_; 
lean_dec_ref(v_eType_362_);
lean_dec_ref(v_env_361_);
v_toPure_369_ = lean_ctor_get(v_toApplicative_360_, 1);
lean_inc(v_toPure_369_);
lean_dec_ref(v_toApplicative_360_);
v___x_370_ = lean_apply_2(v_toPure_369_, lean_box(0), v_e_363_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__0___boxed(lean_object* v_toApplicative_371_, lean_object* v_env_372_, lean_object* v_eType_373_, lean_object* v_e_374_, lean_object* v_____do__lift_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Kernel_toCtorWhenStruct___redArg___lam__0(v_toApplicative_371_, v_env_372_, v_eType_373_, v_e_374_, v_____do__lift_375_);
lean_dec_ref(v_____do__lift_375_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__2(lean_object* v_inductName_377_, lean_object* v_toApplicative_378_, lean_object* v_e_379_, lean_object* v_env_380_, lean_object* v_whnf_381_, lean_object* v_toBind_382_, lean_object* v_inferType_383_, lean_object* v_eType_384_){
_start:
{
lean_object* v___x_385_; uint8_t v___x_386_; 
v___x_385_ = l_Lean_Expr_getAppFn(v_eType_384_);
v___x_386_ = l_Lean_Expr_isConstOf(v___x_385_, v_inductName_377_);
lean_dec_ref(v___x_385_);
if (v___x_386_ == 0)
{
lean_object* v_toPure_387_; lean_object* v___x_388_; 
lean_dec_ref(v_eType_384_);
lean_dec(v_inferType_383_);
lean_dec(v_toBind_382_);
lean_dec(v_whnf_381_);
lean_dec_ref(v_env_380_);
v_toPure_387_ = lean_ctor_get(v_toApplicative_378_, 1);
lean_inc(v_toPure_387_);
lean_dec_ref(v_toApplicative_378_);
v___x_388_ = lean_apply_2(v_toPure_387_, lean_box(0), v_e_379_);
return v___x_388_;
}
else
{
lean_object* v___f_389_; lean_object* v___f_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
lean_inc_ref(v_eType_384_);
v___f_389_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenStruct___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_389_, 0, v_toApplicative_378_);
lean_closure_set(v___f_389_, 1, v_env_380_);
lean_closure_set(v___f_389_, 2, v_eType_384_);
lean_closure_set(v___f_389_, 3, v_e_379_);
lean_inc(v_toBind_382_);
v___f_390_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__6), 4, 3);
lean_closure_set(v___f_390_, 0, v_whnf_381_);
lean_closure_set(v___f_390_, 1, v_toBind_382_);
lean_closure_set(v___f_390_, 2, v___f_389_);
v___x_391_ = lean_apply_1(v_inferType_383_, v_eType_384_);
v___x_392_ = lean_apply_4(v_toBind_382_, lean_box(0), lean_box(0), v___x_391_, v___f_390_);
return v___x_392_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg___lam__2___boxed(lean_object* v_inductName_393_, lean_object* v_toApplicative_394_, lean_object* v_e_395_, lean_object* v_env_396_, lean_object* v_whnf_397_, lean_object* v_toBind_398_, lean_object* v_inferType_399_, lean_object* v_eType_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Lean_Kernel_toCtorWhenStruct___redArg___lam__2(v_inductName_393_, v_toApplicative_394_, v_e_395_, v_env_396_, v_whnf_397_, v_toBind_398_, v_inferType_399_, v_eType_400_);
lean_dec(v_inductName_393_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct___redArg(lean_object* v_inst_402_, lean_object* v_env_403_, lean_object* v_whnf_404_, lean_object* v_inferType_405_, lean_object* v_inductName_406_, lean_object* v_e_407_){
_start:
{
uint8_t v___x_412_; 
lean_inc(v_inductName_406_);
lean_inc_ref(v_env_403_);
v___x_412_ = l_Lean_Kernel_Environment_isStructureLike(v_env_403_, v_inductName_406_);
if (v___x_412_ == 0)
{
lean_dec(v_inductName_406_);
lean_dec(v_inferType_405_);
lean_dec(v_whnf_404_);
lean_dec_ref(v_env_403_);
goto v___jp_408_;
}
else
{
lean_object* v___x_413_; 
lean_inc_ref(v_env_403_);
v___x_413_ = l_Lean_Expr_isConstructorApp_x3f_x27(v_env_403_, v_e_407_);
if (lean_obj_tag(v___x_413_) == 0)
{
lean_object* v_toApplicative_414_; lean_object* v_toBind_415_; lean_object* v___f_416_; lean_object* v___f_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
v_toApplicative_414_ = lean_ctor_get(v_inst_402_, 0);
lean_inc_ref(v_toApplicative_414_);
v_toBind_415_ = lean_ctor_get(v_inst_402_, 1);
lean_inc_n(v_toBind_415_, 3);
lean_dec_ref(v_inst_402_);
lean_inc(v_inferType_405_);
lean_inc(v_whnf_404_);
lean_inc_ref(v_e_407_);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenStruct___redArg___lam__2___boxed), 8, 7);
lean_closure_set(v___f_416_, 0, v_inductName_406_);
lean_closure_set(v___f_416_, 1, v_toApplicative_414_);
lean_closure_set(v___f_416_, 2, v_e_407_);
lean_closure_set(v___f_416_, 3, v_env_403_);
lean_closure_set(v___f_416_, 4, v_whnf_404_);
lean_closure_set(v___f_416_, 5, v_toBind_415_);
lean_closure_set(v___f_416_, 6, v_inferType_405_);
v___f_417_ = lean_alloc_closure((void*)(l_Lean_Kernel_toCtorWhenK___redArg___lam__6), 4, 3);
lean_closure_set(v___f_417_, 0, v_whnf_404_);
lean_closure_set(v___f_417_, 1, v_toBind_415_);
lean_closure_set(v___f_417_, 2, v___f_416_);
v___x_418_ = lean_apply_1(v_inferType_405_, v_e_407_);
v___x_419_ = lean_apply_4(v_toBind_415_, lean_box(0), lean_box(0), v___x_418_, v___f_417_);
return v___x_419_;
}
else
{
lean_dec_ref(v___x_413_);
lean_dec(v_inductName_406_);
lean_dec(v_inferType_405_);
lean_dec(v_whnf_404_);
lean_dec_ref(v_env_403_);
goto v___jp_408_;
}
}
v___jp_408_:
{
lean_object* v_toApplicative_409_; lean_object* v_toPure_410_; lean_object* v___x_411_; 
v_toApplicative_409_ = lean_ctor_get(v_inst_402_, 0);
lean_inc_ref(v_toApplicative_409_);
lean_dec_ref(v_inst_402_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_409_, 1);
lean_inc(v_toPure_410_);
lean_dec_ref(v_toApplicative_409_);
v___x_411_ = lean_apply_2(v_toPure_410_, lean_box(0), v_e_407_);
return v___x_411_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_toCtorWhenStruct(lean_object* v_m_420_, lean_object* v_inst_421_, lean_object* v_env_422_, lean_object* v_whnf_423_, lean_object* v_inferType_424_, lean_object* v_inductName_425_, lean_object* v_e_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_Kernel_toCtorWhenStruct___redArg(v_inst_421_, v_env_422_, v_whnf_423_, v_inferType_424_, v_inductName_425_, v_e_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Kernel_getRecRuleFor_spec__0(lean_object* v_declName_428_, lean_object* v_x_429_){
_start:
{
if (lean_obj_tag(v_x_429_) == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_box(0);
return v___x_430_;
}
else
{
lean_object* v_head_431_; lean_object* v_tail_432_; lean_object* v_ctor_433_; uint8_t v___x_434_; 
v_head_431_ = lean_ctor_get(v_x_429_, 0);
v_tail_432_ = lean_ctor_get(v_x_429_, 1);
v_ctor_433_ = lean_ctor_get(v_head_431_, 0);
v___x_434_ = lean_name_eq(v_ctor_433_, v_declName_428_);
if (v___x_434_ == 0)
{
v_x_429_ = v_tail_432_;
goto _start;
}
else
{
lean_object* v___x_436_; 
lean_inc(v_head_431_);
v___x_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_436_, 0, v_head_431_);
return v___x_436_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Kernel_getRecRuleFor_spec__0___boxed(lean_object* v_declName_437_, lean_object* v_x_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_List_find_x3f___at___00Lean_Kernel_getRecRuleFor_spec__0(v_declName_437_, v_x_438_);
lean_dec(v_x_438_);
lean_dec(v_declName_437_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_getRecRuleFor(lean_object* v_rval_440_, lean_object* v_major_441_){
_start:
{
lean_object* v___x_442_; 
v___x_442_ = l_Lean_Expr_getAppFn(v_major_441_);
if (lean_obj_tag(v___x_442_) == 4)
{
lean_object* v_declName_443_; lean_object* v_rules_444_; lean_object* v___x_445_; 
v_declName_443_ = lean_ctor_get(v___x_442_, 0);
lean_inc(v_declName_443_);
lean_dec_ref(v___x_442_);
v_rules_444_ = lean_ctor_get(v_rval_440_, 6);
v___x_445_ = l_List_find_x3f___at___00Lean_Kernel_getRecRuleFor_spec__0(v_declName_443_, v_rules_444_);
lean_dec(v_declName_443_);
return v___x_445_;
}
else
{
lean_object* v___x_446_; 
lean_dec_ref(v___x_442_);
v___x_446_ = lean_box(0);
return v___x_446_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_getRecRuleFor___boxed(lean_object* v_rval_447_, lean_object* v_major_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l_Lean_Kernel_getRecRuleFor(v_rval_447_, v_major_448_);
lean_dec_ref(v_major_448_);
lean_dec_ref(v_rval_447_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_isOffset_x3f(lean_object* v_x_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = ((lean_object*)(l_Lean_Kernel_isOffset_x3f___closed__2));
v___x_461_ = lean_unsigned_to_nat(1u);
v___x_462_ = l_Lean_Expr_isAppOfArity(v_x_459_, v___x_460_, v___x_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; lean_object* v___x_464_; uint8_t v___x_465_; 
v___x_463_ = ((lean_object*)(l_Lean_Kernel_isOffset_x3f___closed__4));
v___x_464_ = lean_unsigned_to_nat(2u);
v___x_465_ = l_Lean_Expr_isAppOfArity(v_x_459_, v___x_463_, v___x_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
return v___x_466_;
}
else
{
lean_object* v___x_467_; 
v___x_467_ = l_Lean_Expr_appArg_x21(v_x_459_);
if (lean_obj_tag(v___x_467_) == 9)
{
lean_object* v_a_468_; 
v_a_468_ = lean_ctor_get(v___x_467_, 0);
lean_inc_ref(v_a_468_);
lean_dec_ref(v___x_467_);
if (lean_obj_tag(v_a_468_) == 0)
{
lean_object* v_val_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_498_; 
v_val_469_ = lean_ctor_get(v_a_468_, 0);
v_isSharedCheck_498_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_498_ == 0)
{
v___x_471_ = v_a_468_;
v_isShared_472_ = v_isSharedCheck_498_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_val_469_);
lean_dec(v_a_468_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_498_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; 
v___x_473_ = l_Lean_Expr_appFn_x21(v_x_459_);
v___x_474_ = l_Lean_Expr_appArg_x21(v___x_473_);
lean_dec_ref(v___x_473_);
v___x_475_ = l_Lean_Kernel_isOffset_x3f(v___x_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_476_, 0, v___x_474_);
lean_ctor_set(v___x_476_, 1, v_val_469_);
if (v_isShared_472_ == 0)
{
lean_ctor_set_tag(v___x_471_, 1);
lean_ctor_set(v___x_471_, 0, v___x_476_);
v___x_478_ = v___x_471_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_476_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
lean_object* v_val_480_; lean_object* v___x_482_; uint8_t v_isShared_483_; uint8_t v_isSharedCheck_497_; 
lean_dec_ref(v___x_474_);
lean_del_object(v___x_471_);
v_val_480_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_497_ == 0)
{
v___x_482_ = v___x_475_;
v_isShared_483_ = v_isSharedCheck_497_;
goto v_resetjp_481_;
}
else
{
lean_inc(v_val_480_);
lean_dec(v___x_475_);
v___x_482_ = lean_box(0);
v_isShared_483_ = v_isSharedCheck_497_;
goto v_resetjp_481_;
}
v_resetjp_481_:
{
lean_object* v_fst_484_; lean_object* v_snd_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_496_; 
v_fst_484_ = lean_ctor_get(v_val_480_, 0);
v_snd_485_ = lean_ctor_get(v_val_480_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_val_480_);
if (v_isSharedCheck_496_ == 0)
{
v___x_487_ = v_val_480_;
v_isShared_488_ = v_isSharedCheck_496_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_snd_485_);
lean_inc(v_fst_484_);
lean_dec(v_val_480_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_496_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_489_ = lean_nat_add(v_snd_485_, v_val_469_);
lean_dec(v_val_469_);
lean_dec(v_snd_485_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_489_);
v___x_491_ = v___x_487_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_fst_484_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_495_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
lean_object* v___x_493_; 
if (v_isShared_483_ == 0)
{
lean_ctor_set(v___x_482_, 0, v___x_491_);
v___x_493_ = v___x_482_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_499_; 
lean_dec_ref(v_a_468_);
v___x_499_ = lean_box(0);
return v___x_499_;
}
}
else
{
lean_object* v___x_500_; 
lean_dec_ref(v___x_467_);
v___x_500_ = lean_box(0);
return v___x_500_;
}
}
}
else
{
lean_object* v___x_501_; lean_object* v___x_502_; 
v___x_501_ = l_Lean_Expr_appArg_x21(v_x_459_);
v___x_502_ = l_Lean_Kernel_isOffset_x3f(v___x_501_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v___x_503_; lean_object* v___x_504_; 
v___x_503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_503_, 0, v___x_501_);
lean_ctor_set(v___x_503_, 1, v___x_461_);
v___x_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_504_, 0, v___x_503_);
return v___x_504_;
}
else
{
lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v___x_501_);
v_val_505_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_522_ == 0)
{
v___x_507_ = v___x_502_;
v_isShared_508_ = v_isSharedCheck_522_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_dec(v___x_502_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_522_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v_fst_509_; lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_521_; 
v_fst_509_ = lean_ctor_get(v_val_505_, 0);
v_snd_510_ = lean_ctor_get(v_val_505_, 1);
v_isSharedCheck_521_ = !lean_is_exclusive(v_val_505_);
if (v_isSharedCheck_521_ == 0)
{
v___x_512_ = v_val_505_;
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_inc(v_fst_509_);
lean_dec(v_val_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_521_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v___x_516_; 
v___x_514_ = lean_nat_add(v_snd_510_, v___x_461_);
lean_dec(v_snd_510_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v___x_514_);
v___x_516_ = v___x_512_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_fst_509_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v___x_514_);
v___x_516_ = v_reuseFailAlloc_520_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
lean_object* v___x_518_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_516_);
v___x_518_ = v___x_507_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_516_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_isOffset_x3f___boxed(lean_object* v_x_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Kernel_isOffset_x3f(v_x_523_);
lean_dec_ref(v_x_523_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_cleanupNatOffsetMajor(lean_object* v_e_525_){
_start:
{
lean_object* v___x_526_; 
v___x_526_ = l_Lean_Kernel_isOffset_x3f(v_e_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_inc_ref(v_e_525_);
return v_e_525_;
}
else
{
lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_545_; 
v_val_527_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_545_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_545_ == 0)
{
v___x_529_ = v___x_526_;
v_isShared_530_ = v_isSharedCheck_545_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_dec(v___x_526_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_545_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v_fst_531_; lean_object* v_snd_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
v_fst_531_ = lean_ctor_get(v_val_527_, 0);
lean_inc(v_fst_531_);
v_snd_532_ = lean_ctor_get(v_val_527_, 1);
lean_inc(v_snd_532_);
lean_dec(v_val_527_);
v___x_533_ = lean_unsigned_to_nat(0u);
v___x_534_ = lean_nat_dec_eq(v_snd_532_, v___x_533_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_dec_eq(v_snd_532_, v___x_535_);
if (v___x_536_ == 0)
{
lean_object* v___x_537_; lean_object* v___x_539_; 
v___x_537_ = lean_nat_sub(v_snd_532_, v___x_535_);
lean_dec(v_snd_532_);
if (v_isShared_530_ == 0)
{
lean_ctor_set_tag(v___x_529_, 0);
lean_ctor_set(v___x_529_, 0, v___x_537_);
v___x_539_ = v___x_529_;
goto v_reusejp_538_;
}
else
{
lean_object* v_reuseFailAlloc_543_; 
v_reuseFailAlloc_543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_543_, 0, v___x_537_);
v___x_539_ = v_reuseFailAlloc_543_;
goto v_reusejp_538_;
}
v_reusejp_538_:
{
lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_540_ = l_Lean_Expr_lit___override(v___x_539_);
v___x_541_ = l_Lean_mkNatAdd(v_fst_531_, v___x_540_);
v___x_542_ = l_Lean_mkNatSucc(v___x_541_);
return v___x_542_;
}
}
else
{
lean_object* v___x_544_; 
lean_dec(v_snd_532_);
lean_del_object(v___x_529_);
v___x_544_ = l_Lean_mkNatSucc(v_fst_531_);
return v___x_544_;
}
}
else
{
lean_dec(v_snd_532_);
lean_del_object(v___x_529_);
return v_fst_531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_cleanupNatOffsetMajor___boxed(lean_object* v_e_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_Kernel_cleanupNatOffsetMajor(v_e_546_);
lean_dec_ref(v_e_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg(lean_object* v_args_550_, lean_object* v_range_551_, lean_object* v_b_552_, lean_object* v_i_553_){
_start:
{
lean_object* v_stop_554_; lean_object* v_step_555_; uint8_t v___x_556_; 
v_stop_554_ = lean_ctor_get(v_range_551_, 1);
v_step_555_ = lean_ctor_get(v_range_551_, 2);
v___x_556_ = lean_nat_dec_lt(v_i_553_, v_stop_554_);
if (v___x_556_ == 0)
{
lean_dec(v_i_553_);
return v_b_552_;
}
else
{
lean_object* v_snd_557_; lean_object* v___x_559_; uint8_t v_isShared_560_; uint8_t v_isSharedCheck_575_; 
v_snd_557_ = lean_ctor_get(v_b_552_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_b_552_);
if (v_isSharedCheck_575_ == 0)
{
lean_object* v_unused_576_; 
v_unused_576_ = lean_ctor_get(v_b_552_, 0);
lean_dec(v_unused_576_);
v___x_559_ = v_b_552_;
v_isShared_560_ = v_isSharedCheck_575_;
goto v_resetjp_558_;
}
else
{
lean_inc(v_snd_557_);
lean_dec(v_b_552_);
v___x_559_ = lean_box(0);
v_isShared_560_ = v_isSharedCheck_575_;
goto v_resetjp_558_;
}
v_resetjp_558_:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_get_size(v_args_550_);
v___x_562_ = lean_nat_dec_lt(v_i_553_, v___x_561_);
if (v___x_562_ == 0)
{
lean_object* v___x_563_; lean_object* v___x_565_; 
lean_dec(v_i_553_);
v___x_563_ = ((lean_object*)(l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg___closed__0));
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 0, v___x_563_);
v___x_565_ = v___x_559_;
goto v_reusejp_564_;
}
else
{
lean_object* v_reuseFailAlloc_566_; 
v_reuseFailAlloc_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_566_, 0, v___x_563_);
lean_ctor_set(v_reuseFailAlloc_566_, 1, v_snd_557_);
v___x_565_ = v_reuseFailAlloc_566_;
goto v_reusejp_564_;
}
v_reusejp_564_:
{
return v___x_565_;
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_571_; 
v___x_567_ = lean_box(0);
v___x_568_ = lean_array_fget_borrowed(v_args_550_, v_i_553_);
lean_inc(v___x_568_);
v___x_569_ = l_Lean_Expr_app___override(v_snd_557_, v___x_568_);
if (v_isShared_560_ == 0)
{
lean_ctor_set(v___x_559_, 1, v___x_569_);
lean_ctor_set(v___x_559_, 0, v___x_567_);
v___x_571_ = v___x_559_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v___x_567_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v___x_569_);
v___x_571_ = v_reuseFailAlloc_574_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; 
v___x_572_ = lean_nat_add(v_i_553_, v_step_555_);
lean_dec(v_i_553_);
v_b_552_ = v___x_571_;
v_i_553_ = v___x_572_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg___boxed(lean_object* v_args_577_, lean_object* v_range_578_, lean_object* v_b_579_, lean_object* v_i_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg(v_args_577_, v_range_578_, v_b_579_, v_i_580_);
lean_dec_ref(v_range_578_);
lean_dec_ref(v_args_577_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_mkAppRangeChecked(lean_object* v_f_582_, lean_object* v_start_583_, lean_object* v_stop_584_, lean_object* v_args_585_){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v_fst_591_; 
v___x_586_ = lean_unsigned_to_nat(1u);
lean_inc(v_start_583_);
v___x_587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_587_, 0, v_start_583_);
lean_ctor_set(v___x_587_, 1, v_stop_584_);
lean_ctor_set(v___x_587_, 2, v___x_586_);
v___x_588_ = lean_box(0);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_588_);
lean_ctor_set(v___x_589_, 1, v_f_582_);
v___x_590_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg(v_args_585_, v___x_587_, v___x_589_, v_start_583_);
lean_dec_ref(v___x_587_);
v_fst_591_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_fst_591_);
if (lean_obj_tag(v_fst_591_) == 0)
{
lean_object* v_snd_592_; lean_object* v___x_593_; 
v_snd_592_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_snd_592_);
lean_dec_ref(v___x_590_);
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v_snd_592_);
return v___x_593_;
}
else
{
lean_object* v_val_594_; 
lean_dec_ref(v___x_590_);
v_val_594_ = lean_ctor_get(v_fst_591_, 0);
lean_inc(v_val_594_);
lean_dec_ref(v_fst_591_);
return v_val_594_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_mkAppRangeChecked___boxed(lean_object* v_f_595_, lean_object* v_start_596_, lean_object* v_stop_597_, lean_object* v_args_598_){
_start:
{
lean_object* v_res_599_; 
v_res_599_ = l_Lean_Kernel_mkAppRangeChecked(v_f_595_, v_start_596_, v_stop_597_, v_args_598_);
lean_dec_ref(v_args_598_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0(lean_object* v_args_600_, lean_object* v_range_601_, lean_object* v_b_602_, lean_object* v_i_603_, lean_object* v_hs_604_, lean_object* v_hl_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___redArg(v_args_600_, v_range_601_, v_b_602_, v_i_603_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0___boxed(lean_object* v_args_607_, lean_object* v_range_608_, lean_object* v_b_609_, lean_object* v_i_610_, lean_object* v_hs_611_, lean_object* v_hl_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Kernel_mkAppRangeChecked_spec__0(v_args_607_, v_range_608_, v_b_609_, v_i_610_, v_hs_611_, v_hl_612_);
lean_dec_ref(v_range_608_);
lean_dec_ref(v_args_607_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__0(lean_object* v_val_614_, lean_object* v_dummy_615_, lean_object* v___x_616_, lean_object* v_toConstantVal_617_, lean_object* v_us_618_, lean_object* v_toPure_619_, lean_object* v_recArgs_620_, lean_object* v_majorIdx_621_, lean_object* v_____r_622_, lean_object* v_major_623_){
_start:
{
lean_object* v_rhs_625_; lean_object* v___x_628_; 
v___x_628_ = l_Lean_Kernel_getRecRuleFor(v_val_614_, v_major_623_);
if (lean_obj_tag(v___x_628_) == 1)
{
lean_object* v_val_629_; lean_object* v_nfields_630_; lean_object* v_rhs_631_; lean_object* v_nargs_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v_majorArgs_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_val_629_ = lean_ctor_get(v___x_628_, 0);
lean_inc(v_val_629_);
lean_dec_ref(v___x_628_);
v_nfields_630_ = lean_ctor_get(v_val_629_, 1);
lean_inc(v_nfields_630_);
v_rhs_631_ = lean_ctor_get(v_val_629_, 2);
lean_inc_ref(v_rhs_631_);
lean_dec(v_val_629_);
v_nargs_632_ = l_Lean_Expr_getAppNumArgs(v_major_623_);
lean_inc(v_nargs_632_);
v___x_633_ = lean_mk_array(v_nargs_632_, v_dummy_615_);
v___x_634_ = lean_nat_sub(v_nargs_632_, v___x_616_);
lean_dec(v_nargs_632_);
v_majorArgs_635_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_major_623_, v___x_633_, v___x_634_);
v___x_636_ = lean_array_get_size(v_majorArgs_635_);
v___x_637_ = lean_nat_dec_lt(v___x_636_, v_nfields_630_);
if (v___x_637_ == 0)
{
lean_object* v_levelParams_638_; lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v_levelParams_638_ = lean_ctor_get(v_toConstantVal_617_, 1);
lean_inc(v_levelParams_638_);
lean_dec_ref(v_toConstantVal_617_);
v___x_639_ = l_List_lengthTR___redArg(v_us_618_);
v___x_640_ = l_List_lengthTR___redArg(v_levelParams_638_);
v___x_641_ = lean_nat_dec_eq(v___x_639_, v___x_640_);
lean_dec(v___x_640_);
lean_dec(v___x_639_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; 
lean_dec(v_levelParams_638_);
lean_dec_ref(v_majorArgs_635_);
lean_dec_ref(v_rhs_631_);
lean_dec(v_nfields_630_);
lean_dec(v_us_618_);
v___x_642_ = lean_box(0);
v___x_643_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_642_);
return v___x_643_;
}
else
{
lean_object* v_rhs_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; 
v_rhs_644_ = l_Lean_Expr_instantiateLevelParams(v_rhs_631_, v_levelParams_638_, v_us_618_);
lean_dec_ref(v_rhs_631_);
v___x_645_ = lean_unsigned_to_nat(0u);
v___x_646_ = l_Lean_RecursorVal_getFirstIndexIdx(v_val_614_);
v___x_647_ = l_Lean_Kernel_mkAppRangeChecked(v_rhs_644_, v___x_645_, v___x_646_, v_recArgs_620_);
if (lean_obj_tag(v___x_647_) == 1)
{
lean_object* v_val_648_; lean_object* v___x_649_; lean_object* v___x_650_; 
v_val_648_ = lean_ctor_get(v___x_647_, 0);
lean_inc(v_val_648_);
lean_dec_ref(v___x_647_);
v___x_649_ = lean_nat_sub(v___x_636_, v_nfields_630_);
lean_dec(v_nfields_630_);
v___x_650_ = l_Lean_Kernel_mkAppRangeChecked(v_val_648_, v___x_649_, v___x_636_, v_majorArgs_635_);
lean_dec_ref(v_majorArgs_635_);
if (lean_obj_tag(v___x_650_) == 1)
{
lean_object* v_val_651_; lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
v_val_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc(v_val_651_);
lean_dec_ref(v___x_650_);
v___x_652_ = lean_nat_add(v_majorIdx_621_, v___x_616_);
v___x_653_ = lean_array_get_size(v_recArgs_620_);
v___x_654_ = lean_nat_dec_lt(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_dec(v___x_652_);
v_rhs_625_ = v_val_651_;
goto v___jp_624_;
}
else
{
lean_object* v___x_655_; 
v___x_655_ = l_Lean_Kernel_mkAppRangeChecked(v_val_651_, v___x_652_, v___x_653_, v_recArgs_620_);
if (lean_obj_tag(v___x_655_) == 1)
{
lean_object* v_val_656_; 
v_val_656_ = lean_ctor_get(v___x_655_, 0);
lean_inc(v_val_656_);
lean_dec_ref(v___x_655_);
v_rhs_625_ = v_val_656_;
goto v___jp_624_;
}
else
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v___x_655_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_657_);
return v___x_658_;
}
}
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; 
lean_dec(v___x_650_);
v___x_659_ = lean_box(0);
v___x_660_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_659_);
return v___x_660_;
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; 
lean_dec(v___x_647_);
lean_dec_ref(v_majorArgs_635_);
lean_dec(v_nfields_630_);
v___x_661_ = lean_box(0);
v___x_662_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_661_);
return v___x_662_;
}
}
}
else
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec_ref(v_majorArgs_635_);
lean_dec_ref(v_rhs_631_);
lean_dec(v_nfields_630_);
lean_dec(v_us_618_);
lean_dec_ref(v_toConstantVal_617_);
v___x_663_ = lean_box(0);
v___x_664_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_663_);
return v___x_664_;
}
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v___x_628_);
lean_dec_ref(v_major_623_);
lean_dec(v_us_618_);
lean_dec_ref(v_toConstantVal_617_);
lean_dec_ref(v_dummy_615_);
v___x_665_ = lean_box(0);
v___x_666_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_665_);
return v___x_666_;
}
v___jp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v_rhs_625_);
v___x_627_ = lean_apply_2(v_toPure_619_, lean_box(0), v___x_626_);
return v___x_627_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__0___boxed(lean_object* v_val_667_, lean_object* v_dummy_668_, lean_object* v___x_669_, lean_object* v_toConstantVal_670_, lean_object* v_us_671_, lean_object* v_toPure_672_, lean_object* v_recArgs_673_, lean_object* v_majorIdx_674_, lean_object* v_____r_675_, lean_object* v_major_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_Kernel_inductiveReduceRec___redArg___lam__0(v_val_667_, v_dummy_668_, v___x_669_, v_toConstantVal_670_, v_us_671_, v_toPure_672_, v_recArgs_673_, v_majorIdx_674_, v_____r_675_, v_major_676_);
lean_dec(v_majorIdx_674_);
lean_dec_ref(v_recArgs_673_);
lean_dec(v___x_669_);
lean_dec_ref(v_val_667_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__1(lean_object* v___f_678_, lean_object* v_major_679_){
_start:
{
lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_680_ = lean_box(0);
v___x_681_ = lean_apply_2(v___f_678_, v___x_680_, v_major_679_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__3(lean_object* v___f_682_, lean_object* v_whnf_683_, lean_object* v_toBind_684_, lean_object* v___f_685_, lean_object* v_val_686_, lean_object* v_inst_687_, lean_object* v_env_688_, lean_object* v_inferType_689_, lean_object* v___f_690_, lean_object* v_____do__lift_691_){
_start:
{
if (lean_obj_tag(v_____do__lift_691_) == 9)
{
lean_object* v_a_692_; 
lean_dec(v___f_690_);
lean_dec(v_inferType_689_);
lean_dec_ref(v_env_688_);
lean_dec_ref(v_inst_687_);
lean_dec_ref(v_val_686_);
v_a_692_ = lean_ctor_get(v_____do__lift_691_, 0);
lean_inc_ref(v_a_692_);
lean_dec_ref(v_____do__lift_691_);
if (lean_obj_tag(v_a_692_) == 0)
{
lean_object* v_val_693_; lean_object* v_major_694_; lean_object* v___x_695_; lean_object* v___x_696_; 
lean_dec(v___f_685_);
lean_dec(v_toBind_684_);
lean_dec(v_whnf_683_);
v_val_693_ = lean_ctor_get(v_a_692_, 0);
lean_inc(v_val_693_);
lean_dec_ref(v_a_692_);
v_major_694_ = l_Lean_Expr_natLitToConstructor(v_val_693_);
lean_dec(v_val_693_);
v___x_695_ = lean_box(0);
v___x_696_ = lean_apply_2(v___f_682_, v___x_695_, v_major_694_);
return v___x_696_;
}
else
{
lean_object* v_val_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; 
lean_dec(v___f_682_);
v_val_697_ = lean_ctor_get(v_a_692_, 0);
lean_inc_ref(v_val_697_);
lean_dec_ref(v_a_692_);
v___x_698_ = l_Lean_Expr_strLitToConstructor(v_val_697_);
v___x_699_ = lean_apply_1(v_whnf_683_, v___x_698_);
v___x_700_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_699_, v___f_685_);
return v___x_700_;
}
}
else
{
lean_object* v_major_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
lean_dec(v___f_685_);
lean_dec(v___f_682_);
v_major_701_ = l_Lean_Kernel_cleanupNatOffsetMajor(v_____do__lift_691_);
lean_dec_ref(v_____do__lift_691_);
v___x_702_ = l_Lean_RecursorVal_getMajorInduct(v_val_686_);
v___x_703_ = l_Lean_Kernel_toCtorWhenStruct___redArg(v_inst_687_, v_env_688_, v_whnf_683_, v_inferType_689_, v___x_702_, v_major_701_);
v___x_704_ = lean_apply_4(v_toBind_684_, lean_box(0), lean_box(0), v___x_703_, v___f_690_);
return v___x_704_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg___lam__2(lean_object* v_whnf_705_, lean_object* v_toBind_706_, lean_object* v___f_707_, lean_object* v_____r_708_, lean_object* v_major_709_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_apply_1(v_whnf_705_, v_major_709_);
v___x_711_ = lean_apply_4(v_toBind_706_, lean_box(0), lean_box(0), v___x_710_, v___f_707_);
return v___x_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec___redArg(lean_object* v_inst_712_, lean_object* v_env_713_, lean_object* v_e_714_, lean_object* v_whnf_715_, lean_object* v_inferType_716_, lean_object* v_isDefEq_717_){
_start:
{
lean_object* v_toApplicative_718_; lean_object* v_toBind_719_; lean_object* v_toPure_720_; lean_object* v___x_724_; 
v_toApplicative_718_ = lean_ctor_get(v_inst_712_, 0);
v_toBind_719_ = lean_ctor_get(v_inst_712_, 1);
lean_inc(v_toBind_719_);
v_toPure_720_ = lean_ctor_get(v_toApplicative_718_, 1);
v___x_724_ = l_Lean_Expr_getAppFn(v_e_714_);
if (lean_obj_tag(v___x_724_) == 4)
{
lean_object* v_declName_725_; lean_object* v_us_726_; lean_object* v___x_727_; 
v_declName_725_ = lean_ctor_get(v___x_724_, 0);
lean_inc(v_declName_725_);
v_us_726_ = lean_ctor_get(v___x_724_, 1);
lean_inc(v_us_726_);
lean_dec_ref(v___x_724_);
lean_inc_ref(v_env_713_);
v___x_727_ = lean_environment_find(v_env_713_, v_declName_725_);
if (lean_obj_tag(v___x_727_) == 1)
{
lean_object* v_val_728_; 
v_val_728_ = lean_ctor_get(v___x_727_, 0);
lean_inc(v_val_728_);
lean_dec_ref(v___x_727_);
if (lean_obj_tag(v_val_728_) == 7)
{
lean_object* v_val_729_; lean_object* v_dummy_730_; lean_object* v_nargs_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v_recArgs_735_; lean_object* v_majorIdx_736_; lean_object* v___x_737_; uint8_t v___x_738_; 
v_val_729_ = lean_ctor_get(v_val_728_, 0);
lean_inc_ref(v_val_729_);
lean_dec_ref(v_val_728_);
v_dummy_730_ = lean_obj_once(&l_Lean_Kernel_mkNullaryCtor___closed__0, &l_Lean_Kernel_mkNullaryCtor___closed__0_once, _init_l_Lean_Kernel_mkNullaryCtor___closed__0);
v_nargs_731_ = l_Lean_Expr_getAppNumArgs(v_e_714_);
lean_inc(v_nargs_731_);
v___x_732_ = lean_mk_array(v_nargs_731_, v_dummy_730_);
v___x_733_ = lean_unsigned_to_nat(1u);
v___x_734_ = lean_nat_sub(v_nargs_731_, v___x_733_);
lean_dec(v_nargs_731_);
v_recArgs_735_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_714_, v___x_732_, v___x_734_);
v_majorIdx_736_ = l_Lean_RecursorVal_getMajorIdx(v_val_729_);
v___x_737_ = lean_array_get_size(v_recArgs_735_);
v___x_738_ = lean_nat_dec_lt(v_majorIdx_736_, v___x_737_);
if (v___x_738_ == 0)
{
lean_object* v___x_739_; lean_object* v___x_740_; 
lean_inc(v_toPure_720_);
lean_dec(v_majorIdx_736_);
lean_dec_ref(v_recArgs_735_);
lean_dec_ref(v_val_729_);
lean_dec(v_us_726_);
lean_dec(v_toBind_719_);
lean_dec(v_isDefEq_717_);
lean_dec(v_inferType_716_);
lean_dec(v_whnf_715_);
lean_dec_ref(v_env_713_);
lean_dec_ref(v_inst_712_);
v___x_739_ = lean_box(0);
v___x_740_ = lean_apply_2(v_toPure_720_, lean_box(0), v___x_739_);
return v___x_740_;
}
else
{
lean_object* v_toConstantVal_741_; uint8_t v_k_742_; lean_object* v___f_743_; lean_object* v___f_744_; lean_object* v___f_745_; lean_object* v___f_746_; lean_object* v___x_747_; 
v_toConstantVal_741_ = lean_ctor_get(v_val_729_, 0);
v_k_742_ = lean_ctor_get_uint8(v_val_729_, sizeof(void*)*7);
lean_inc(v_majorIdx_736_);
lean_inc_ref(v_recArgs_735_);
lean_inc(v_toPure_720_);
lean_inc_ref(v_toConstantVal_741_);
lean_inc_ref_n(v_val_729_, 2);
v___f_743_ = lean_alloc_closure((void*)(l_Lean_Kernel_inductiveReduceRec___redArg___lam__0___boxed), 10, 8);
lean_closure_set(v___f_743_, 0, v_val_729_);
lean_closure_set(v___f_743_, 1, v_dummy_730_);
lean_closure_set(v___f_743_, 2, v___x_733_);
lean_closure_set(v___f_743_, 3, v_toConstantVal_741_);
lean_closure_set(v___f_743_, 4, v_us_726_);
lean_closure_set(v___f_743_, 5, v_toPure_720_);
lean_closure_set(v___f_743_, 6, v_recArgs_735_);
lean_closure_set(v___f_743_, 7, v_majorIdx_736_);
lean_inc_ref(v___f_743_);
v___f_744_ = lean_alloc_closure((void*)(l_Lean_Kernel_inductiveReduceRec___redArg___lam__1), 2, 1);
lean_closure_set(v___f_744_, 0, v___f_743_);
lean_inc(v_inferType_716_);
lean_inc_ref(v_env_713_);
lean_inc_ref(v_inst_712_);
lean_inc_ref(v___f_744_);
lean_inc_n(v_toBind_719_, 2);
lean_inc_n(v_whnf_715_, 2);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Kernel_inductiveReduceRec___redArg___lam__3), 10, 9);
lean_closure_set(v___f_745_, 0, v___f_743_);
lean_closure_set(v___f_745_, 1, v_whnf_715_);
lean_closure_set(v___f_745_, 2, v_toBind_719_);
lean_closure_set(v___f_745_, 3, v___f_744_);
lean_closure_set(v___f_745_, 4, v_val_729_);
lean_closure_set(v___f_745_, 5, v_inst_712_);
lean_closure_set(v___f_745_, 6, v_env_713_);
lean_closure_set(v___f_745_, 7, v_inferType_716_);
lean_closure_set(v___f_745_, 8, v___f_744_);
lean_inc_ref(v___f_745_);
v___f_746_ = lean_alloc_closure((void*)(l_Lean_Kernel_inductiveReduceRec___redArg___lam__2), 5, 3);
lean_closure_set(v___f_746_, 0, v_whnf_715_);
lean_closure_set(v___f_746_, 1, v_toBind_719_);
lean_closure_set(v___f_746_, 2, v___f_745_);
v___x_747_ = lean_array_fget(v_recArgs_735_, v_majorIdx_736_);
lean_dec(v_majorIdx_736_);
lean_dec_ref(v_recArgs_735_);
if (v_k_742_ == 0)
{
lean_object* v___x_748_; lean_object* v___x_749_; 
lean_dec_ref(v___f_746_);
lean_dec_ref(v_val_729_);
lean_dec(v_isDefEq_717_);
lean_dec(v_inferType_716_);
lean_dec_ref(v_env_713_);
lean_dec_ref(v_inst_712_);
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_Kernel_inductiveReduceRec___redArg___lam__2(v_whnf_715_, v_toBind_719_, v___f_745_, v___x_748_, v___x_747_);
return v___x_749_;
}
else
{
lean_object* v___f_750_; lean_object* v___x_751_; lean_object* v___x_752_; 
lean_dec_ref(v___f_745_);
v___f_750_ = lean_alloc_closure((void*)(l_Lean_Kernel_inductiveReduceRec___redArg___lam__1), 2, 1);
lean_closure_set(v___f_750_, 0, v___f_746_);
v___x_751_ = l_Lean_Kernel_toCtorWhenK___redArg(v_inst_712_, v_env_713_, v_whnf_715_, v_inferType_716_, v_isDefEq_717_, v_val_729_, v___x_747_);
v___x_752_ = lean_apply_4(v_toBind_719_, lean_box(0), lean_box(0), v___x_751_, v___f_750_);
return v___x_752_;
}
}
}
else
{
lean_inc(v_toPure_720_);
lean_dec(v_val_728_);
lean_dec(v_us_726_);
lean_dec(v_toBind_719_);
lean_dec(v_isDefEq_717_);
lean_dec(v_inferType_716_);
lean_dec(v_whnf_715_);
lean_dec_ref(v_e_714_);
lean_dec_ref(v_env_713_);
lean_dec_ref(v_inst_712_);
goto v___jp_721_;
}
}
else
{
lean_inc(v_toPure_720_);
lean_dec(v___x_727_);
lean_dec(v_us_726_);
lean_dec(v_toBind_719_);
lean_dec(v_isDefEq_717_);
lean_dec(v_inferType_716_);
lean_dec(v_whnf_715_);
lean_dec_ref(v_e_714_);
lean_dec_ref(v_env_713_);
lean_dec_ref(v_inst_712_);
goto v___jp_721_;
}
}
else
{
lean_object* v___x_753_; lean_object* v___x_754_; 
lean_inc(v_toPure_720_);
lean_dec_ref(v___x_724_);
lean_dec(v_toBind_719_);
lean_dec(v_isDefEq_717_);
lean_dec(v_inferType_716_);
lean_dec(v_whnf_715_);
lean_dec_ref(v_e_714_);
lean_dec_ref(v_env_713_);
lean_dec_ref(v_inst_712_);
v___x_753_ = lean_box(0);
v___x_754_ = lean_apply_2(v_toPure_720_, lean_box(0), v___x_753_);
return v___x_754_;
}
v___jp_721_:
{
lean_object* v___x_722_; lean_object* v___x_723_; 
v___x_722_ = lean_box(0);
v___x_723_ = lean_apply_2(v_toPure_720_, lean_box(0), v___x_722_);
return v___x_723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_inductiveReduceRec(lean_object* v_m_755_, lean_object* v_inst_756_, lean_object* v_env_757_, lean_object* v_e_758_, lean_object* v_whnf_759_, lean_object* v_inferType_760_, lean_object* v_isDefEq_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_Kernel_inductiveReduceRec___redArg(v_inst_756_, v_env_757_, v_e_758_, v_whnf_759_, v_inferType_760_, v_isDefEq_761_);
return v___x_762_;
}
}
lean_object* runtime_initialize_Lean_Structure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_Recognizers(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Inductive_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Inductive_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Structure(uint8_t builtin);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Expr(uint8_t builtin);
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Inductive_Reduce(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Structure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Inductive_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Inductive_Reduce(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Inductive_Reduce(builtin);
}
#ifdef __cplusplus
}
#endif
