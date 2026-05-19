// Lean compiler output
// Module: Lean.Kernel.Quot
// Imports: public import Lean.Environment public import Lean.Kernel.Expr public import Lean.Kernel.Instantiate public import Lean.Kernel.LocalContext
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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
extern lean_object* l_Lean_Expr_prop;
lean_object* l_Lean_Expr_arrow(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkForall(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* lean_environment_add(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_environment_mark_quot_init(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Environment_get(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Kernel_ExprBuildT_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Kernel_ExprBuildT_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Kernel_ExprBuildT_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Kernel_ExprBuildT_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__3;
static lean_once_cell_t l_Lean_Kernel_ExprBuildT_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__4;
static const lean_string_object l_Lean_Kernel_ExprBuildT_run___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "_uniq"};
static const lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__5 = (const lean_object*)&l_Lean_Kernel_ExprBuildT_run___redArg___closed__5_value;
static const lean_ctor_object l_Lean_Kernel_ExprBuildT_run___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_ExprBuildT_run___redArg___closed__5_value),LEAN_SCALAR_PTR_LITERAL(237, 141, 162, 170, 202, 74, 55, 55)}};
static const lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__6 = (const lean_object*)&l_Lean_Kernel_ExprBuildT_run___redArg___closed__6_value;
static const lean_ctor_object l_Lean_Kernel_ExprBuildT_run___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Kernel_ExprBuildT_run___redArg___closed__6_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Kernel_ExprBuildT_run___redArg___closed__7 = (const lean_object*)&l_Lean_Kernel_ExprBuildT_run___redArg___closed__7_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT___closed__0 = (const lean_object*)&l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___at___00Lean_Kernel_checkEqType_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___at___00Lean_Kernel_checkEqType_spec__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_checkEqType___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "failed to initialize quot module, "};
static const lean_object* l_Lean_Kernel_checkEqType___lam__0___closed__0 = (const lean_object*)&l_Lean_Kernel_checkEqType___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_checkEqType___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 62, .m_capacity = 62, .m_length = 61, .m_data = "unexpected number of universe params at 'Eq' type constructor"};
static const lean_object* l_Lean_Kernel_checkEqType___lam__1___closed__0 = (const lean_object*)&l_Lean_Kernel_checkEqType___lam__1___closed__0_value;
static const lean_string_object l_Lean_Kernel_checkEqType___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l_Lean_Kernel_checkEqType___lam__1___closed__1 = (const lean_object*)&l_Lean_Kernel_checkEqType___lam__1___closed__1_value;
static const lean_ctor_object l_Lean_Kernel_checkEqType___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_checkEqType___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l_Lean_Kernel_checkEqType___lam__1___closed__2 = (const lean_object*)&l_Lean_Kernel_checkEqType___lam__1___closed__2_value;
static const lean_string_object l_Lean_Kernel_checkEqType___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "unexpected type for 'Eq' type constructor"};
static const lean_object* l_Lean_Kernel_checkEqType___lam__1___closed__3 = (const lean_object*)&l_Lean_Kernel_checkEqType___lam__1___closed__3_value;
static const lean_ctor_object l_Lean_Kernel_checkEqType___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Kernel_checkEqType___lam__1___closed__4 = (const lean_object*)&l_Lean_Kernel_checkEqType___lam__1___closed__4_value;
static const lean_string_object l_Lean_Kernel_checkEqType___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "'Eq' has an expected type"};
static const lean_object* l_Lean_Kernel_checkEqType___lam__1___closed__5 = (const lean_object*)&l_Lean_Kernel_checkEqType___lam__1___closed__5_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_checkEqType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Kernel_checkEqType___closed__0 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__0_value;
static const lean_ctor_object l_Lean_Kernel_checkEqType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_checkEqType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Kernel_checkEqType___closed__1 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__1_value;
static const lean_closure_object l_Lean_Kernel_checkEqType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Kernel_checkEqType___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Kernel_checkEqType___closed__2 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__2_value;
static const lean_string_object l_Lean_Kernel_checkEqType___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 48, .m_capacity = 48, .m_length = 47, .m_data = "unexpected number of constructors for 'Eq' type"};
static const lean_object* l_Lean_Kernel_checkEqType___closed__3 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__3_value;
static lean_once_cell_t l_Lean_Kernel_checkEqType___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_checkEqType___closed__4;
static const lean_string_object l_Lean_Kernel_checkEqType___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "unexpected number of universe params at 'Eq' type"};
static const lean_object* l_Lean_Kernel_checkEqType___closed__5 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__5_value;
static lean_once_cell_t l_Lean_Kernel_checkEqType___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_checkEqType___closed__6;
static const lean_string_object l_Lean_Kernel_checkEqType___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "α"};
static const lean_object* l_Lean_Kernel_checkEqType___closed__7 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__7_value;
static const lean_ctor_object l_Lean_Kernel_checkEqType___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_checkEqType___closed__7_value),LEAN_SCALAR_PTR_LITERAL(102, 24, 27, 80, 217, 159, 184, 13)}};
static const lean_object* l_Lean_Kernel_checkEqType___closed__8 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__8_value;
static const lean_string_object l_Lean_Kernel_checkEqType___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "environment does not have 'Eq' type"};
static const lean_object* l_Lean_Kernel_checkEqType___closed__9 = (const lean_object*)&l_Lean_Kernel_checkEqType___closed__9_value;
static lean_once_cell_t l_Lean_Kernel_checkEqType___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_checkEqType___closed__10;
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType(lean_object*);
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "r"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__0 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(201, 206, 29, 183, 206, 15, 98, 41)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__1 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__1_value;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__2 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__3 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__3_value;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__4 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__4_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__5_value_aux_0),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__5 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__5_value;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "v"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__6 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__6_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(166, 108, 188, 174, 117, 112, 110, 72)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__7 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Kernel_Environment_addQuot___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__8;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "β"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__9 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__9_value),LEAN_SCALAR_PTR_LITERAL(163, 67, 89, 131, 111, 186, 232, 248)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__10 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Kernel_Environment_addQuot___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__11;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "f"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__12 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(29, 68, 183, 24, 128, 148, 178, 23)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__13 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__13_value;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__14 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__15 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__15_value;
static lean_once_cell_t l_Lean_Kernel_Environment_addQuot___lam__0___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__16;
static lean_once_cell_t l_Lean_Kernel_Environment_addQuot___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__17;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__18 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__19 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__19_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__20 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__20_value;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "q"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__21 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__21_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__21_value),LEAN_SCALAR_PTR_LITERAL(111, 208, 133, 57, 225, 251, 103, 73)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__22 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__22_value;
static const lean_string_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ind"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__23 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__23_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__24_value_aux_0),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__23_value),LEAN_SCALAR_PTR_LITERAL(150, 213, 121, 152, 109, 27, 137, 60)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__24 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__24_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___lam__0___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__4_value),LEAN_SCALAR_PTR_LITERAL(223, 214, 247, 82, 130, 198, 123, 173)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___closed__25 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___lam__0___closed__25_value;
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addQuot___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Kernel_Environment_addQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "u"};
static const lean_object* l_Lean_Kernel_Environment_addQuot___closed__0 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___closed__0_value;
static const lean_ctor_object l_Lean_Kernel_Environment_addQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Kernel_Environment_addQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 178, 247, 241, 102, 42, 87, 174)}};
static const lean_object* l_Lean_Kernel_Environment_addQuot___closed__1 = (const lean_object*)&l_Lean_Kernel_Environment_addQuot___closed__1_value;
static lean_once_cell_t l_Lean_Kernel_Environment_addQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Environment_addQuot___closed__2;
static lean_once_cell_t l_Lean_Kernel_Environment_addQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_Environment_addQuot___closed__3;
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addQuot(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Kernel_quotReduceRec___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Kernel_quotReduceRec___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_Kernel_ExprBuildT_run___redArg___closed__0, &l_Lean_Kernel_ExprBuildT_run___redArg___closed__0_once, _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_4_ = lean_unsigned_to_nat(32u);
v___x_5_ = lean_mk_empty_array_with_capacity(v___x_4_);
v___x_6_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
static lean_object* _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__3(void){
_start:
{
size_t v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = ((size_t)5ULL);
v___x_8_ = lean_unsigned_to_nat(0u);
v___x_9_ = lean_unsigned_to_nat(32u);
v___x_10_ = lean_mk_empty_array_with_capacity(v___x_9_);
v___x_11_ = lean_obj_once(&l_Lean_Kernel_ExprBuildT_run___redArg___closed__2, &l_Lean_Kernel_ExprBuildT_run___redArg___closed__2_once, _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__2);
v___x_12_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_12_, 0, v___x_11_);
lean_ctor_set(v___x_12_, 1, v___x_10_);
lean_ctor_set(v___x_12_, 2, v___x_8_);
lean_ctor_set(v___x_12_, 3, v___x_8_);
lean_ctor_set_usize(v___x_12_, 4, v___x_7_);
return v___x_12_;
}
}
static lean_object* _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__4(void){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_13_ = lean_box(1);
v___x_14_ = lean_obj_once(&l_Lean_Kernel_ExprBuildT_run___redArg___closed__3, &l_Lean_Kernel_ExprBuildT_run___redArg___closed__3_once, _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__3);
v___x_15_ = lean_obj_once(&l_Lean_Kernel_ExprBuildT_run___redArg___closed__1, &l_Lean_Kernel_ExprBuildT_run___redArg___closed__1_once, _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__1);
v___x_16_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
lean_ctor_set(v___x_16_, 2, v___x_13_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___redArg(lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_24_ = lean_obj_once(&l_Lean_Kernel_ExprBuildT_run___redArg___closed__4, &l_Lean_Kernel_ExprBuildT_run___redArg___closed__4_once, _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__4);
v___x_25_ = ((lean_object*)(l_Lean_Kernel_ExprBuildT_run___redArg___closed__7));
v___x_26_ = lean_apply_2(v_x_23_, v___x_24_, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run(lean_object* v_m_27_, lean_object* v_00_u03b1_28_, lean_object* v_inst_29_, lean_object* v_x_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Lean_Kernel_ExprBuildT_run___redArg(v_x_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___boxed(lean_object* v_m_32_, lean_object* v_00_u03b1_33_, lean_object* v_inst_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_Lean_Kernel_ExprBuildT_run(v_m_32_, v_00_u03b1_33_, v_inst_34_, v_x_35_);
lean_dec_ref(v_inst_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT___lam__0(lean_object* v_00_u03b1_37_, lean_object* v_x_38_, lean_object* v_c_39_, lean_object* v_ngen_40_){
_start:
{
lean_object* v_namePrefix_41_; lean_object* v_idx_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_53_; 
v_namePrefix_41_ = lean_ctor_get(v_ngen_40_, 0);
v_idx_42_ = lean_ctor_get(v_ngen_40_, 1);
v_isSharedCheck_53_ = !lean_is_exclusive(v_ngen_40_);
if (v_isSharedCheck_53_ == 0)
{
v___x_44_ = v_ngen_40_;
v_isShared_45_ = v_isSharedCheck_53_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_idx_42_);
lean_inc(v_namePrefix_41_);
lean_dec(v_ngen_40_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_53_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_50_; 
lean_inc(v_idx_42_);
lean_inc(v_namePrefix_41_);
v___x_46_ = l_Lean_Name_num___override(v_namePrefix_41_, v_idx_42_);
v___x_47_ = lean_unsigned_to_nat(1u);
v___x_48_ = lean_nat_add(v_idx_42_, v___x_47_);
lean_dec(v_idx_42_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 1, v___x_48_);
v___x_50_ = v___x_44_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_52_; 
v_reuseFailAlloc_52_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_52_, 0, v_namePrefix_41_);
lean_ctor_set(v_reuseFailAlloc_52_, 1, v___x_48_);
v___x_50_ = v_reuseFailAlloc_52_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_51_; 
v___x_51_ = lean_apply_3(v_x_38_, v___x_46_, v_c_39_, v___x_50_);
return v___x_51_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT(lean_object* v_m_55_){
_start:
{
lean_object* v___f_56_; 
v___f_56_ = ((lean_object*)(l_Lean_Kernel_instMonadLocalNameGeneratorExprBuildT___closed__0));
return v___f_56_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___at___00Lean_Kernel_checkEqType_spec__0___redArg(lean_object* v_x_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_58_ = lean_unsigned_to_nat(32u);
v___x_59_ = lean_mk_empty_array_with_capacity(v___x_58_);
lean_dec_ref(v___x_59_);
v___x_60_ = lean_obj_once(&l_Lean_Kernel_ExprBuildT_run___redArg___closed__4, &l_Lean_Kernel_ExprBuildT_run___redArg___closed__4_once, _init_l_Lean_Kernel_ExprBuildT_run___redArg___closed__4);
v___x_61_ = ((lean_object*)(l_Lean_Kernel_ExprBuildT_run___redArg___closed__7));
v___x_62_ = lean_apply_2(v_x_57_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_ExprBuildT_run___at___00Lean_Kernel_checkEqType_spec__0(lean_object* v_00_u03b1_63_, lean_object* v_x_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Lean_Kernel_ExprBuildT_run___at___00Lean_Kernel_checkEqType_spec__0___redArg(v_x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__0(lean_object* v_00_u03b1_67_, lean_object* v_s_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_69_ = ((lean_object*)(l_Lean_Kernel_checkEqType___lam__0___closed__0));
v___x_70_ = lean_string_append(v___x_69_, v_s_68_);
v___x_71_ = lean_alloc_ctor(12, 1, 0);
lean_ctor_set(v___x_71_, 0, v___x_70_);
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
return v___x_72_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__0___boxed(lean_object* v_00_u03b1_73_, lean_object* v_s_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lean_Kernel_checkEqType___lam__0(v_00_u03b1_73_, v_s_74_);
lean_dec_ref(v_s_74_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__1(lean_object* v_fail_84_, lean_object* v_env_85_, lean_object* v_head_86_, lean_object* v___x_87_, uint8_t v___x_88_, lean_object* v___x_89_, lean_object* v___x_90_, lean_object* v_type_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_namePrefix_97_; lean_object* v_idx_98_; lean_object* v___x_149_; lean_object* v___x_150_; uint8_t v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
v_namePrefix_97_ = lean_ctor_get(v___y_93_, 0);
v_idx_98_ = lean_ctor_get(v___y_93_, 1);
lean_inc(v_idx_98_);
lean_inc(v_namePrefix_97_);
v___x_149_ = l_Lean_Name_num___override(v_namePrefix_97_, v_idx_98_);
lean_inc(v___x_149_);
v___x_150_ = l_Lean_Expr_fvar___override(v___x_149_);
v___x_151_ = 0;
lean_inc(v___x_87_);
lean_inc_ref(v___y_92_);
v___x_152_ = l_Lean_LocalContext_mkLocalDecl(v___y_92_, v___x_149_, v___x_87_, v___x_90_, v___x_88_, v___x_151_);
v___x_153_ = lean_unsigned_to_nat(1u);
v___x_154_ = lean_mk_empty_array_with_capacity(v___x_153_);
lean_inc_ref_n(v___x_150_, 2);
v___x_155_ = lean_array_push(v___x_154_, v___x_150_);
v___x_156_ = l_Lean_Expr_prop;
v___x_157_ = l_Lean_Expr_arrow(v___x_150_, v___x_156_);
v___x_158_ = l_Lean_Expr_arrow(v___x_150_, v___x_157_);
v___x_159_ = 1;
v___x_160_ = 0;
v___x_161_ = l_Lean_LocalContext_mkForall(v___x_152_, v___x_155_, v___x_158_, v___x_159_, v___x_160_);
lean_dec_ref(v___x_158_);
lean_dec_ref(v___x_155_);
v___x_162_ = lean_expr_eqv(v_type_91_, v___x_161_);
lean_dec_ref(v___x_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Kernel_checkEqType___lam__1___closed__5));
lean_inc_ref(v_fail_84_);
v___x_164_ = lean_apply_2(v_fail_84_, lean_box(0), v___x_163_);
if (lean_obj_tag(v___x_164_) == 0)
{
lean_dec(v___x_89_);
lean_dec(v___x_87_);
lean_dec(v_head_86_);
lean_dec_ref(v_env_85_);
lean_dec_ref(v_fail_84_);
return v___x_164_;
}
else
{
lean_dec_ref(v___x_164_);
goto v___jp_99_;
}
}
else
{
goto v___jp_99_;
}
v___jp_94_:
{
lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_95_ = ((lean_object*)(l_Lean_Kernel_checkEqType___lam__1___closed__0));
v___x_96_ = lean_apply_2(v_fail_84_, lean_box(0), v___x_95_);
return v___x_96_;
}
v___jp_99_:
{
lean_object* v___x_100_; 
v___x_100_ = l_Lean_Kernel_Environment_get(v_env_85_, v_head_86_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_108_; 
lean_dec(v___x_89_);
lean_dec(v___x_87_);
lean_dec_ref(v_fail_84_);
v_a_101_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_108_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_108_ == 0)
{
v___x_103_ = v___x_100_;
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_a_101_);
lean_dec(v___x_100_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_108_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v_a_101_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
else
{
lean_object* v_a_109_; lean_object* v___x_110_; 
v_a_109_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_109_);
lean_dec_ref(v___x_100_);
v___x_110_ = l_Lean_ConstantInfo_levelParams(v_a_109_);
if (lean_obj_tag(v___x_110_) == 1)
{
lean_object* v_tail_111_; 
v_tail_111_ = lean_ctor_get(v___x_110_, 1);
lean_inc(v_tail_111_);
if (lean_obj_tag(v_tail_111_) == 0)
{
lean_object* v_head_112_; lean_object* v___x_114_; uint8_t v_isShared_115_; uint8_t v_isSharedCheck_147_; 
v_head_112_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_147_ == 0)
{
lean_object* v_unused_148_; 
v_unused_148_ = lean_ctor_get(v___x_110_, 1);
lean_dec(v_unused_148_);
v___x_114_ = v___x_110_;
v_isShared_115_ = v_isSharedCheck_147_;
goto v_resetjp_113_;
}
else
{
lean_inc(v_head_112_);
lean_dec(v___x_110_);
v___x_114_ = lean_box(0);
v_isShared_115_ = v_isSharedCheck_147_;
goto v_resetjp_113_;
}
v_resetjp_113_:
{
lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; uint8_t v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_116_ = l_Lean_Level_param___override(v_head_112_);
lean_inc(v___x_116_);
v___x_117_ = l_Lean_Expr_sort___override(v___x_116_);
lean_inc(v_idx_98_);
lean_inc_n(v_namePrefix_97_, 2);
v___x_118_ = l_Lean_Name_num___override(v_namePrefix_97_, v_idx_98_);
v___x_119_ = lean_unsigned_to_nat(1u);
v___x_120_ = lean_nat_add(v_idx_98_, v___x_119_);
lean_inc(v___x_118_);
v___x_121_ = l_Lean_Expr_fvar___override(v___x_118_);
v___x_122_ = 0;
lean_inc_ref(v___y_92_);
v___x_123_ = l_Lean_LocalContext_mkLocalDecl(v___y_92_, v___x_118_, v___x_87_, v___x_117_, v___x_88_, v___x_122_);
v___x_124_ = ((lean_object*)(l_Lean_Kernel_checkEqType___lam__1___closed__2));
v___x_125_ = 0;
v___x_126_ = l_Lean_Name_num___override(v_namePrefix_97_, v___x_120_);
lean_inc(v___x_126_);
v___x_127_ = l_Lean_Expr_fvar___override(v___x_126_);
lean_inc_ref_n(v___x_121_, 2);
v___x_128_ = l_Lean_LocalContext_mkLocalDecl(v___x_123_, v___x_126_, v___x_124_, v___x_121_, v___x_125_, v___x_122_);
v___x_129_ = l_Lean_ConstantInfo_type(v_a_109_);
lean_dec(v_a_109_);
v___x_130_ = lean_unsigned_to_nat(2u);
v___x_131_ = lean_mk_empty_array_with_capacity(v___x_130_);
v___x_132_ = lean_array_push(v___x_131_, v___x_121_);
lean_inc_ref(v___x_127_);
v___x_133_ = lean_array_push(v___x_132_, v___x_127_);
v___x_134_ = lean_box(0);
if (v_isShared_115_ == 0)
{
lean_ctor_set(v___x_114_, 1, v___x_134_);
lean_ctor_set(v___x_114_, 0, v___x_116_);
v___x_136_ = v___x_114_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_116_);
lean_ctor_set(v_reuseFailAlloc_146_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_146_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; uint8_t v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v___x_137_ = l_Lean_Expr_const___override(v___x_89_, v___x_136_);
lean_inc_ref(v___x_127_);
v___x_138_ = l_Lean_mkApp3(v___x_137_, v___x_121_, v___x_127_, v___x_127_);
v___x_139_ = 1;
v___x_140_ = 0;
v___x_141_ = l_Lean_LocalContext_mkForall(v___x_128_, v___x_133_, v___x_138_, v___x_139_, v___x_140_);
lean_dec_ref(v___x_138_);
lean_dec_ref(v___x_133_);
v___x_142_ = lean_expr_eqv(v___x_129_, v___x_141_);
lean_dec_ref(v___x_141_);
lean_dec_ref(v___x_129_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Kernel_checkEqType___lam__1___closed__3));
v___x_144_ = lean_apply_2(v_fail_84_, lean_box(0), v___x_143_);
return v___x_144_;
}
else
{
lean_object* v___x_145_; 
lean_dec_ref(v_fail_84_);
v___x_145_ = ((lean_object*)(l_Lean_Kernel_checkEqType___lam__1___closed__4));
return v___x_145_;
}
}
}
}
else
{
lean_dec(v_tail_111_);
lean_dec_ref(v___x_110_);
lean_dec(v_a_109_);
lean_dec(v___x_89_);
lean_dec(v___x_87_);
goto v___jp_94_;
}
}
else
{
lean_dec(v___x_110_);
lean_dec(v_a_109_);
lean_dec(v___x_89_);
lean_dec(v___x_87_);
goto v___jp_94_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType___lam__1___boxed(lean_object* v_fail_165_, lean_object* v_env_166_, lean_object* v_head_167_, lean_object* v___x_168_, lean_object* v___x_169_, lean_object* v___x_170_, lean_object* v___x_171_, lean_object* v_type_172_, lean_object* v___y_173_, lean_object* v___y_174_){
_start:
{
uint8_t v___x_4627__boxed_175_; lean_object* v_res_176_; 
v___x_4627__boxed_175_ = lean_unbox(v___x_169_);
v_res_176_ = l_Lean_Kernel_checkEqType___lam__1(v_fail_165_, v_env_166_, v_head_167_, v___x_168_, v___x_4627__boxed_175_, v___x_170_, v___x_171_, v_type_172_, v___y_173_, v___y_174_);
lean_dec_ref(v___y_174_);
lean_dec_ref(v___y_173_);
lean_dec_ref(v_type_172_);
return v_res_176_;
}
}
static lean_object* _init_l_Lean_Kernel_checkEqType___closed__4(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__3));
v___x_183_ = l_Lean_Kernel_checkEqType___lam__0(lean_box(0), v___x_182_);
return v___x_183_;
}
}
static lean_object* _init_l_Lean_Kernel_checkEqType___closed__6(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_185_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__5));
v___x_186_ = l_Lean_Kernel_checkEqType___lam__0(lean_box(0), v___x_185_);
return v___x_186_;
}
}
static lean_object* _init_l_Lean_Kernel_checkEqType___closed__10(void){
_start:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__9));
v___x_192_ = l_Lean_Kernel_checkEqType___lam__0(lean_box(0), v___x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_checkEqType(lean_object* v_env_193_){
_start:
{
lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_194_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__1));
lean_inc_ref(v_env_193_);
v___x_195_ = l_Lean_Kernel_Environment_get(v_env_193_, v___x_194_);
if (lean_obj_tag(v___x_195_) == 0)
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
lean_dec_ref(v_env_193_);
v_a_196_ = lean_ctor_get(v___x_195_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_195_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_195_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_195_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
else
{
lean_object* v_a_204_; lean_object* v_fail_205_; 
v_a_204_ = lean_ctor_get(v___x_195_, 0);
lean_inc(v_a_204_);
lean_dec_ref(v___x_195_);
v_fail_205_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__2));
if (lean_obj_tag(v_a_204_) == 5)
{
lean_object* v_val_210_; lean_object* v_toConstantVal_211_; lean_object* v_levelParams_212_; 
v_val_210_ = lean_ctor_get(v_a_204_, 0);
lean_inc_ref(v_val_210_);
lean_dec_ref(v_a_204_);
v_toConstantVal_211_ = lean_ctor_get(v_val_210_, 0);
lean_inc_ref(v_toConstantVal_211_);
v_levelParams_212_ = lean_ctor_get(v_toConstantVal_211_, 1);
lean_inc(v_levelParams_212_);
if (lean_obj_tag(v_levelParams_212_) == 1)
{
lean_object* v_tail_213_; 
v_tail_213_ = lean_ctor_get(v_levelParams_212_, 1);
if (lean_obj_tag(v_tail_213_) == 0)
{
lean_object* v_ctors_214_; 
v_ctors_214_ = lean_ctor_get(v_val_210_, 4);
lean_inc(v_ctors_214_);
lean_dec_ref(v_val_210_);
if (lean_obj_tag(v_ctors_214_) == 1)
{
lean_object* v_tail_215_; 
v_tail_215_ = lean_ctor_get(v_ctors_214_, 1);
if (lean_obj_tag(v_tail_215_) == 0)
{
lean_object* v_type_216_; lean_object* v_head_217_; lean_object* v_head_218_; lean_object* v___x_219_; uint8_t v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___f_224_; lean_object* v___x_225_; 
v_type_216_ = lean_ctor_get(v_toConstantVal_211_, 2);
lean_inc_ref(v_type_216_);
lean_dec_ref(v_toConstantVal_211_);
v_head_217_ = lean_ctor_get(v_levelParams_212_, 0);
lean_inc(v_head_217_);
lean_dec_ref(v_levelParams_212_);
v_head_218_ = lean_ctor_get(v_ctors_214_, 0);
lean_inc(v_head_218_);
lean_dec_ref(v_ctors_214_);
v___x_219_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__8));
v___x_220_ = 1;
v___x_221_ = l_Lean_Level_param___override(v_head_217_);
v___x_222_ = l_Lean_Expr_sort___override(v___x_221_);
v___x_223_ = lean_box(v___x_220_);
v___f_224_ = lean_alloc_closure((void*)(l_Lean_Kernel_checkEqType___lam__1___boxed), 10, 8);
lean_closure_set(v___f_224_, 0, v_fail_205_);
lean_closure_set(v___f_224_, 1, v_env_193_);
lean_closure_set(v___f_224_, 2, v_head_218_);
lean_closure_set(v___f_224_, 3, v___x_219_);
lean_closure_set(v___f_224_, 4, v___x_223_);
lean_closure_set(v___f_224_, 5, v___x_194_);
lean_closure_set(v___f_224_, 6, v___x_222_);
lean_closure_set(v___f_224_, 7, v_type_216_);
v___x_225_ = l_Lean_Kernel_ExprBuildT_run___at___00Lean_Kernel_checkEqType_spec__0___redArg(v___f_224_);
return v___x_225_;
}
else
{
lean_dec_ref(v_ctors_214_);
lean_dec_ref(v_levelParams_212_);
lean_dec_ref(v_toConstantVal_211_);
lean_dec_ref(v_env_193_);
goto v___jp_206_;
}
}
else
{
lean_dec(v_ctors_214_);
lean_dec_ref(v_levelParams_212_);
lean_dec_ref(v_toConstantVal_211_);
lean_dec_ref(v_env_193_);
goto v___jp_206_;
}
}
else
{
lean_dec_ref(v_levelParams_212_);
lean_dec_ref(v_toConstantVal_211_);
lean_dec_ref(v_val_210_);
lean_dec_ref(v_env_193_);
goto v___jp_208_;
}
}
else
{
lean_dec(v_levelParams_212_);
lean_dec_ref(v_toConstantVal_211_);
lean_dec_ref(v_val_210_);
lean_dec_ref(v_env_193_);
goto v___jp_208_;
}
}
else
{
lean_object* v___x_226_; 
lean_dec(v_a_204_);
lean_dec_ref(v_env_193_);
v___x_226_ = lean_obj_once(&l_Lean_Kernel_checkEqType___closed__10, &l_Lean_Kernel_checkEqType___closed__10_once, _init_l_Lean_Kernel_checkEqType___closed__10);
return v___x_226_;
}
v___jp_206_:
{
lean_object* v___x_207_; 
v___x_207_ = lean_obj_once(&l_Lean_Kernel_checkEqType___closed__4, &l_Lean_Kernel_checkEqType___closed__4_once, _init_l_Lean_Kernel_checkEqType___closed__4);
return v___x_207_;
}
v___jp_208_:
{
lean_object* v___x_209_; 
v___x_209_ = lean_obj_once(&l_Lean_Kernel_checkEqType___closed__6, &l_Lean_Kernel_checkEqType___closed__6_once, _init_l_Lean_Kernel_checkEqType___closed__6);
return v___x_209_;
}
}
}
}
static lean_object* _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__8(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__7));
v___x_241_ = l_Lean_Level_param___override(v___x_240_);
return v___x_241_;
}
}
static lean_object* _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__11(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___lam__0___closed__8, &l_Lean_Kernel_Environment_addQuot___lam__0___closed__8_once, _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__8);
v___x_246_ = l_Lean_Expr_sort___override(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__16(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = lean_box(0);
v___x_254_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___lam__0___closed__8, &l_Lean_Kernel_Environment_addQuot___lam__0___closed__8_once, _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__8);
v___x_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___x_253_);
return v___x_255_;
}
}
static lean_object* _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__17(void){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_256_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___lam__0___closed__16, &l_Lean_Kernel_Environment_addQuot___lam__0___closed__16_once, _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__16);
v___x_257_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__1));
v___x_258_ = l_Lean_Expr_const___override(v___x_257_, v___x_256_);
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addQuot___lam__0(lean_object* v___x_275_, lean_object* v___x_276_, uint8_t v___x_277_, lean_object* v___x_278_, uint8_t v___x_279_, uint8_t v_quotInit_280_, lean_object* v_env_281_, lean_object* v___x_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v_namePrefix_285_; lean_object* v_idx_286_; lean_object* v___x_288_; uint8_t v_isShared_289_; uint8_t v_isSharedCheck_409_; 
v_namePrefix_285_ = lean_ctor_get(v___y_284_, 0);
v_idx_286_ = lean_ctor_get(v___y_284_, 1);
v_isSharedCheck_409_ = !lean_is_exclusive(v___y_284_);
if (v_isSharedCheck_409_ == 0)
{
v___x_288_ = v___y_284_;
v_isShared_289_ = v_isSharedCheck_409_;
goto v_resetjp_287_;
}
else
{
lean_inc(v_idx_286_);
lean_inc(v_namePrefix_285_);
lean_dec(v___y_284_);
v___x_288_ = lean_box(0);
v_isShared_289_ = v_isSharedCheck_409_;
goto v_resetjp_287_;
}
v_resetjp_287_:
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; uint8_t v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_308_; 
lean_inc(v_idx_286_);
lean_inc_n(v_namePrefix_285_, 2);
v___x_290_ = l_Lean_Name_num___override(v_namePrefix_285_, v_idx_286_);
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_idx_286_, v___x_291_);
lean_dec(v_idx_286_);
lean_inc(v___x_290_);
v___x_293_ = l_Lean_Expr_fvar___override(v___x_290_);
v___x_294_ = 0;
lean_inc_ref(v___x_276_);
v___x_295_ = l_Lean_LocalContext_mkLocalDecl(v___y_283_, v___x_290_, v___x_275_, v___x_276_, v___x_277_, v___x_294_);
v___x_296_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__1));
v___x_297_ = 0;
v___x_298_ = l_Lean_Expr_prop;
lean_inc_ref_n(v___x_293_, 2);
v___x_299_ = l_Lean_Expr_arrow(v___x_293_, v___x_298_);
v___x_300_ = l_Lean_Expr_arrow(v___x_293_, v___x_299_);
lean_inc(v___x_292_);
v___x_301_ = l_Lean_Name_num___override(v_namePrefix_285_, v___x_292_);
v___x_302_ = lean_nat_add(v___x_292_, v___x_291_);
lean_dec(v___x_292_);
lean_inc_n(v___x_301_, 2);
v___x_303_ = l_Lean_Expr_fvar___override(v___x_301_);
lean_inc_ref(v___x_300_);
lean_inc_ref(v___x_295_);
v___x_304_ = l_Lean_LocalContext_mkLocalDecl(v___x_295_, v___x_301_, v___x_296_, v___x_300_, v___x_297_, v___x_294_);
v___x_305_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__3));
v___x_306_ = lean_box(0);
lean_inc(v___x_278_);
if (v_isShared_289_ == 0)
{
lean_ctor_set_tag(v___x_288_, 1);
lean_ctor_set(v___x_288_, 1, v___x_306_);
lean_ctor_set(v___x_288_, 0, v___x_278_);
v___x_308_ = v___x_288_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_408_; 
v_reuseFailAlloc_408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_408_, 0, v___x_278_);
lean_ctor_set(v_reuseFailAlloc_408_, 1, v___x_306_);
v___x_308_ = v_reuseFailAlloc_408_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; uint8_t v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v___x_309_ = lean_unsigned_to_nat(2u);
v___x_310_ = lean_mk_empty_array_with_capacity(v___x_309_);
lean_inc_ref_n(v___x_293_, 8);
lean_inc_ref(v___x_310_);
v___x_311_ = lean_array_push(v___x_310_, v___x_293_);
lean_inc_ref_n(v___x_303_, 5);
v___x_312_ = lean_array_push(v___x_311_, v___x_303_);
lean_inc_ref(v___x_304_);
v___x_313_ = l_Lean_LocalContext_mkForall(v___x_304_, v___x_312_, v___x_276_, v___x_279_, v_quotInit_280_);
lean_dec_ref(v___x_276_);
lean_dec_ref(v___x_312_);
lean_inc_ref_n(v___x_308_, 2);
v___x_314_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_314_, 0, v___x_305_);
lean_ctor_set(v___x_314_, 1, v___x_308_);
lean_ctor_set(v___x_314_, 2, v___x_313_);
v___x_315_ = 0;
v___x_316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set_uint8(v___x_316_, sizeof(void*)*1, v___x_315_);
v___x_317_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
v___x_318_ = lean_environment_add(v_env_281_, v___x_317_);
v___x_319_ = ((lean_object*)(l_Lean_Kernel_checkEqType___lam__1___closed__2));
lean_inc(v___x_302_);
lean_inc_n(v_namePrefix_285_, 3);
v___x_320_ = l_Lean_Name_num___override(v_namePrefix_285_, v___x_302_);
lean_inc_n(v___x_320_, 2);
v___x_321_ = l_Lean_Expr_fvar___override(v___x_320_);
v___x_322_ = l_Lean_LocalContext_mkLocalDecl(v___x_304_, v___x_320_, v___x_319_, v___x_293_, v___x_297_, v___x_294_);
v___x_323_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__5));
v___x_324_ = lean_unsigned_to_nat(3u);
v___x_325_ = lean_mk_empty_array_with_capacity(v___x_324_);
v___x_326_ = lean_array_push(v___x_325_, v___x_293_);
v___x_327_ = lean_array_push(v___x_326_, v___x_303_);
lean_inc_ref_n(v___x_321_, 5);
lean_inc_ref(v___x_327_);
v___x_328_ = lean_array_push(v___x_327_, v___x_321_);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_282_);
lean_ctor_set(v___x_329_, 1, v___x_306_);
lean_inc_ref(v___x_329_);
v___x_330_ = l_Lean_Expr_const___override(v___x_305_, v___x_329_);
v___x_331_ = l_Lean_mkAppB(v___x_330_, v___x_293_, v___x_303_);
v___x_332_ = l_Lean_LocalContext_mkForall(v___x_322_, v___x_328_, v___x_331_, v___x_279_, v_quotInit_280_);
lean_dec_ref(v___x_328_);
v___x_333_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_333_, 0, v___x_323_);
lean_ctor_set(v___x_333_, 1, v___x_308_);
lean_ctor_set(v___x_333_, 2, v___x_332_);
v___x_334_ = 1;
v___x_335_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_335_, 0, v___x_333_);
lean_ctor_set_uint8(v___x_335_, sizeof(void*)*1, v___x_334_);
v___x_336_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
v___x_337_ = lean_environment_add(v___x_318_, v___x_336_);
v___x_338_ = l_Lean_LocalContext_mkLocalDecl(v___x_295_, v___x_301_, v___x_296_, v___x_300_, v___x_277_, v___x_294_);
v___x_339_ = lean_nat_add(v___x_302_, v___x_291_);
lean_dec(v___x_302_);
v___x_340_ = l_Lean_LocalContext_mkLocalDecl(v___x_338_, v___x_320_, v___x_319_, v___x_293_, v___x_297_, v___x_294_);
v___x_341_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__10));
v___x_342_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___lam__0___closed__11, &l_Lean_Kernel_Environment_addQuot___lam__0___closed__11_once, _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__11);
lean_inc(v___x_339_);
v___x_343_ = l_Lean_Name_num___override(v_namePrefix_285_, v___x_339_);
v___x_344_ = lean_nat_add(v___x_339_, v___x_291_);
lean_dec(v___x_339_);
lean_inc_n(v___x_343_, 2);
v___x_345_ = l_Lean_Expr_fvar___override(v___x_343_);
lean_inc_ref(v___x_340_);
v___x_346_ = l_Lean_LocalContext_mkLocalDecl(v___x_340_, v___x_343_, v___x_341_, v___x_342_, v___x_277_, v___x_294_);
v___x_347_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__13));
lean_inc_ref_n(v___x_345_, 6);
v___x_348_ = l_Lean_Expr_arrow(v___x_293_, v___x_345_);
lean_inc(v___x_344_);
v___x_349_ = l_Lean_Name_num___override(v_namePrefix_285_, v___x_344_);
v___x_350_ = lean_nat_add(v___x_344_, v___x_291_);
lean_dec(v___x_344_);
lean_inc_n(v___x_349_, 2);
v___x_351_ = l_Lean_Expr_fvar___override(v___x_349_);
v___x_352_ = l_Lean_LocalContext_mkLocalDecl(v___x_346_, v___x_349_, v___x_347_, v___x_348_, v___x_297_, v___x_294_);
v___x_353_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__15));
v___x_354_ = l_Lean_Name_num___override(v_namePrefix_285_, v___x_350_);
lean_inc(v___x_354_);
v___x_355_ = l_Lean_Expr_fvar___override(v___x_354_);
v___x_356_ = l_Lean_LocalContext_mkLocalDecl(v___x_352_, v___x_354_, v___x_353_, v___x_293_, v___x_297_, v___x_294_);
lean_inc_ref_n(v___x_355_, 2);
v___x_357_ = l_Lean_mkAppB(v___x_303_, v___x_321_, v___x_355_);
v___x_358_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___lam__0___closed__17, &l_Lean_Kernel_Environment_addQuot___lam__0___closed__17_once, _init_l_Lean_Kernel_Environment_addQuot___lam__0___closed__17);
lean_inc_ref_n(v___x_351_, 4);
v___x_359_ = l_Lean_Expr_app___override(v___x_351_, v___x_321_);
v___x_360_ = l_Lean_Expr_app___override(v___x_351_, v___x_355_);
v___x_361_ = l_Lean_mkApp3(v___x_358_, v___x_345_, v___x_359_, v___x_360_);
v___x_362_ = lean_array_push(v___x_310_, v___x_321_);
v___x_363_ = lean_array_push(v___x_362_, v___x_355_);
v___x_364_ = l_Lean_Expr_arrow(v___x_357_, v___x_361_);
lean_inc_ref(v___x_356_);
v___x_365_ = l_Lean_LocalContext_mkForall(v___x_356_, v___x_363_, v___x_364_, v___x_279_, v_quotInit_280_);
lean_dec_ref(v___x_364_);
lean_dec_ref(v___x_363_);
v___x_366_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__19));
v___x_367_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__20));
v___x_368_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_278_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_unsigned_to_nat(4u);
v___x_370_ = lean_mk_empty_array_with_capacity(v___x_369_);
v___x_371_ = lean_array_push(v___x_370_, v___x_293_);
v___x_372_ = lean_array_push(v___x_371_, v___x_303_);
v___x_373_ = lean_array_push(v___x_372_, v___x_345_);
v___x_374_ = lean_array_push(v___x_373_, v___x_351_);
lean_inc_ref_n(v___x_331_, 2);
v___x_375_ = l_Lean_Expr_arrow(v___x_331_, v___x_345_);
v___x_376_ = l_Lean_Expr_arrow(v___x_365_, v___x_375_);
v___x_377_ = l_Lean_LocalContext_mkForall(v___x_356_, v___x_374_, v___x_376_, v___x_279_, v_quotInit_280_);
lean_dec_ref(v___x_376_);
lean_dec_ref(v___x_374_);
v___x_378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_378_, 0, v___x_366_);
lean_ctor_set(v___x_378_, 1, v___x_368_);
lean_ctor_set(v___x_378_, 2, v___x_377_);
v___x_379_ = 2;
v___x_380_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_380_, 0, v___x_378_);
lean_ctor_set_uint8(v___x_380_, sizeof(void*)*1, v___x_379_);
v___x_381_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_381_, 0, v___x_380_);
v___x_382_ = lean_environment_add(v___x_337_, v___x_381_);
v___x_383_ = l_Lean_Expr_const___override(v___x_323_, v___x_329_);
v___x_384_ = l_Lean_mkApp3(v___x_383_, v___x_293_, v___x_303_, v___x_321_);
v___x_385_ = l_Lean_Expr_arrow(v___x_331_, v___x_298_);
v___x_386_ = l_Lean_LocalContext_mkLocalDecl(v___x_340_, v___x_343_, v___x_341_, v___x_385_, v___x_277_, v___x_294_);
v___x_387_ = lean_mk_empty_array_with_capacity(v___x_291_);
lean_inc_ref(v___x_387_);
v___x_388_ = lean_array_push(v___x_387_, v___x_321_);
v___x_389_ = l_Lean_Expr_app___override(v___x_345_, v___x_384_);
lean_inc_ref(v___x_386_);
v___x_390_ = l_Lean_LocalContext_mkForall(v___x_386_, v___x_388_, v___x_389_, v___x_279_, v_quotInit_280_);
lean_dec_ref(v___x_389_);
lean_dec_ref(v___x_388_);
v___x_391_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__22));
v___x_392_ = l_Lean_LocalContext_mkLocalDecl(v___x_386_, v___x_349_, v___x_391_, v___x_331_, v___x_277_, v___x_294_);
v___x_393_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__24));
v___x_394_ = lean_array_push(v___x_327_, v___x_345_);
v___x_395_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__25));
v___x_396_ = lean_array_push(v___x_387_, v___x_351_);
v___x_397_ = l_Lean_Expr_app___override(v___x_345_, v___x_351_);
lean_inc_ref(v___x_392_);
v___x_398_ = l_Lean_LocalContext_mkForall(v___x_392_, v___x_396_, v___x_397_, v___x_279_, v_quotInit_280_);
lean_dec_ref(v___x_397_);
lean_dec_ref(v___x_396_);
v___x_399_ = l_Lean_Expr_forallE___override(v___x_395_, v___x_390_, v___x_398_, v___x_297_);
v___x_400_ = l_Lean_LocalContext_mkForall(v___x_392_, v___x_394_, v___x_399_, v___x_279_, v_quotInit_280_);
lean_dec_ref(v___x_399_);
lean_dec_ref(v___x_394_);
v___x_401_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_401_, 0, v___x_393_);
lean_ctor_set(v___x_401_, 1, v___x_308_);
lean_ctor_set(v___x_401_, 2, v___x_400_);
v___x_402_ = 3;
v___x_403_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_403_, 0, v___x_401_);
lean_ctor_set_uint8(v___x_403_, sizeof(void*)*1, v___x_402_);
v___x_404_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
v___x_405_ = lean_environment_add(v___x_382_, v___x_404_);
v___x_406_ = lean_environment_mark_quot_init(v___x_405_);
v___x_407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
return v___x_407_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addQuot___lam__0___boxed(lean_object* v___x_410_, lean_object* v___x_411_, lean_object* v___x_412_, lean_object* v___x_413_, lean_object* v___x_414_, lean_object* v_quotInit_415_, lean_object* v_env_416_, lean_object* v___x_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
uint8_t v___x_14253__boxed_420_; uint8_t v___x_14255__boxed_421_; uint8_t v_quotInit_boxed_422_; lean_object* v_res_423_; 
v___x_14253__boxed_420_ = lean_unbox(v___x_412_);
v___x_14255__boxed_421_ = lean_unbox(v___x_414_);
v_quotInit_boxed_422_ = lean_unbox(v_quotInit_415_);
v_res_423_ = l_Lean_Kernel_Environment_addQuot___lam__0(v___x_410_, v___x_411_, v___x_14253__boxed_420_, v___x_413_, v___x_14255__boxed_421_, v_quotInit_boxed_422_, v_env_416_, v___x_417_, v___y_418_, v___y_419_);
return v_res_423_;
}
}
static lean_object* _init_l_Lean_Kernel_Environment_addQuot___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___closed__1));
v___x_428_ = l_Lean_Level_param___override(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l_Lean_Kernel_Environment_addQuot___closed__3(void){
_start:
{
lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_429_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___closed__2, &l_Lean_Kernel_Environment_addQuot___closed__2_once, _init_l_Lean_Kernel_Environment_addQuot___closed__2);
v___x_430_ = l_Lean_Expr_sort___override(v___x_429_);
return v___x_430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addQuot(lean_object* v_env_431_){
_start:
{
uint8_t v_quotInit_432_; 
v_quotInit_432_ = lean_ctor_get_uint8(v_env_431_, sizeof(void*)*6);
if (v_quotInit_432_ == 0)
{
lean_object* v___x_433_; 
lean_inc_ref(v_env_431_);
v___x_433_ = l_Lean_Kernel_checkEqType(v_env_431_);
if (lean_obj_tag(v___x_433_) == 0)
{
lean_object* v_a_434_; lean_object* v___x_436_; uint8_t v_isShared_437_; uint8_t v_isSharedCheck_441_; 
lean_dec_ref(v_env_431_);
v_a_434_ = lean_ctor_get(v___x_433_, 0);
v_isSharedCheck_441_ = !lean_is_exclusive(v___x_433_);
if (v_isSharedCheck_441_ == 0)
{
v___x_436_ = v___x_433_;
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
else
{
lean_inc(v_a_434_);
lean_dec(v___x_433_);
v___x_436_ = lean_box(0);
v_isShared_437_ = v_isSharedCheck_441_;
goto v_resetjp_435_;
}
v_resetjp_435_:
{
lean_object* v___x_439_; 
if (v_isShared_437_ == 0)
{
v___x_439_ = v___x_436_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_434_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
else
{
uint8_t v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; uint8_t v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___f_451_; lean_object* v___x_452_; 
lean_dec_ref(v___x_433_);
v___x_442_ = 1;
v___x_443_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___closed__1));
v___x_444_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___closed__2, &l_Lean_Kernel_Environment_addQuot___closed__2_once, _init_l_Lean_Kernel_Environment_addQuot___closed__2);
v___x_445_ = ((lean_object*)(l_Lean_Kernel_checkEqType___closed__8));
v___x_446_ = 1;
v___x_447_ = lean_obj_once(&l_Lean_Kernel_Environment_addQuot___closed__3, &l_Lean_Kernel_Environment_addQuot___closed__3_once, _init_l_Lean_Kernel_Environment_addQuot___closed__3);
v___x_448_ = lean_box(v___x_446_);
v___x_449_ = lean_box(v___x_442_);
v___x_450_ = lean_box(v_quotInit_432_);
v___f_451_ = lean_alloc_closure((void*)(l_Lean_Kernel_Environment_addQuot___lam__0___boxed), 10, 8);
lean_closure_set(v___f_451_, 0, v___x_445_);
lean_closure_set(v___f_451_, 1, v___x_447_);
lean_closure_set(v___f_451_, 2, v___x_448_);
lean_closure_set(v___f_451_, 3, v___x_443_);
lean_closure_set(v___f_451_, 4, v___x_449_);
lean_closure_set(v___f_451_, 5, v___x_450_);
lean_closure_set(v___f_451_, 6, v_env_431_);
lean_closure_set(v___f_451_, 7, v___x_444_);
v___x_452_ = l_Lean_Kernel_ExprBuildT_run___at___00Lean_Kernel_checkEqType_spec__0___redArg(v___f_451_);
return v___x_452_;
}
}
else
{
lean_object* v___x_453_; 
v___x_453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_453_, 0, v_env_431_);
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec___redArg___lam__0(lean_object* v_toPure_454_, lean_object* v_args_455_, lean_object* v_argPos_456_, lean_object* v_mkPos_457_, lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v_mk_460_){
_start:
{
lean_object* v_r_462_; lean_object* v___x_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v___x_465_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__5));
v___x_466_ = lean_unsigned_to_nat(3u);
v___x_467_ = l_Lean_Expr_isAppOfArity(v_mk_460_, v___x_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_box(0);
v___x_469_ = lean_apply_2(v_toPure_454_, lean_box(0), v___x_468_);
return v___x_469_;
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v_r_473_; lean_object* v_elimArity_474_; uint8_t v___x_475_; 
v___x_470_ = l_Lean_instInhabitedExpr;
v___x_471_ = lean_array_get_borrowed(v___x_470_, v_args_455_, v_argPos_456_);
v___x_472_ = l_Lean_Expr_appArg_x21(v_mk_460_);
lean_inc(v___x_471_);
v_r_473_ = l_Lean_Expr_app___override(v___x_471_, v___x_472_);
v_elimArity_474_ = lean_nat_add(v_mkPos_457_, v___x_458_);
v___x_475_ = lean_nat_dec_lt(v_elimArity_474_, v___x_459_);
if (v___x_475_ == 0)
{
lean_dec(v_elimArity_474_);
v_r_462_ = v_r_473_;
goto v___jp_461_;
}
else
{
lean_object* v_r_476_; 
v_r_476_ = l_Lean_mkAppRange(v_r_473_, v_elimArity_474_, v___x_459_, v_args_455_);
v_r_462_ = v_r_476_;
goto v___jp_461_;
}
}
v___jp_461_:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_463_, 0, v_r_462_);
v___x_464_ = lean_apply_2(v_toPure_454_, lean_box(0), v___x_463_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec___redArg___lam__0___boxed(lean_object* v_toPure_477_, lean_object* v_args_478_, lean_object* v_argPos_479_, lean_object* v_mkPos_480_, lean_object* v___x_481_, lean_object* v___x_482_, lean_object* v_mk_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l_Lean_Kernel_quotReduceRec___redArg___lam__0(v_toPure_477_, v_args_478_, v_argPos_479_, v_mkPos_480_, v___x_481_, v___x_482_, v_mk_483_);
lean_dec_ref(v_mk_483_);
lean_dec(v___x_482_);
lean_dec(v___x_481_);
lean_dec(v_mkPos_480_);
lean_dec(v_argPos_479_);
lean_dec_ref(v_args_478_);
return v_res_484_;
}
}
static lean_object* _init_l_Lean_Kernel_quotReduceRec___redArg___closed__0(void){
_start:
{
lean_object* v___x_485_; lean_object* v_dummy_486_; 
v___x_485_ = lean_box(0);
v_dummy_486_ = l_Lean_Expr_sort___override(v___x_485_);
return v_dummy_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec___redArg(lean_object* v_inst_487_, lean_object* v_e_488_, lean_object* v_whnf_489_){
_start:
{
lean_object* v_toApplicative_490_; lean_object* v_toBind_491_; lean_object* v_toPure_492_; lean_object* v_mkPos_494_; lean_object* v_argPos_495_; lean_object* v___x_510_; 
v_toApplicative_490_ = lean_ctor_get(v_inst_487_, 0);
lean_inc_ref(v_toApplicative_490_);
v_toBind_491_ = lean_ctor_get(v_inst_487_, 1);
lean_inc(v_toBind_491_);
lean_dec_ref(v_inst_487_);
v_toPure_492_ = lean_ctor_get(v_toApplicative_490_, 1);
lean_inc(v_toPure_492_);
lean_dec_ref(v_toApplicative_490_);
v___x_510_ = l_Lean_Expr_getAppFn(v_e_488_);
if (lean_obj_tag(v___x_510_) == 4)
{
lean_object* v_declName_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_declName_511_ = lean_ctor_get(v___x_510_, 0);
lean_inc(v_declName_511_);
lean_dec_ref(v___x_510_);
v___x_512_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__19));
v___x_513_ = lean_name_eq(v_declName_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_object* v___x_514_; uint8_t v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Kernel_Environment_addQuot___lam__0___closed__24));
v___x_515_ = lean_name_eq(v_declName_511_, v___x_514_);
lean_dec(v_declName_511_);
if (v___x_515_ == 0)
{
lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec(v_toBind_491_);
lean_dec(v_whnf_489_);
lean_dec_ref(v_e_488_);
v___x_516_ = lean_box(0);
v___x_517_ = lean_apply_2(v_toPure_492_, lean_box(0), v___x_516_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(4u);
v___x_519_ = lean_unsigned_to_nat(3u);
v_mkPos_494_ = v___x_518_;
v_argPos_495_ = v___x_519_;
goto v___jp_493_;
}
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_declName_511_);
v___x_520_ = lean_unsigned_to_nat(5u);
v___x_521_ = lean_unsigned_to_nat(3u);
v_mkPos_494_ = v___x_520_;
v_argPos_495_ = v___x_521_;
goto v___jp_493_;
}
}
else
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v___x_510_);
lean_dec(v_toBind_491_);
lean_dec(v_whnf_489_);
lean_dec_ref(v_e_488_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_2(v_toPure_492_, lean_box(0), v___x_522_);
return v___x_523_;
}
v___jp_493_:
{
lean_object* v_dummy_496_; lean_object* v_nargs_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v_args_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v_dummy_496_ = lean_obj_once(&l_Lean_Kernel_quotReduceRec___redArg___closed__0, &l_Lean_Kernel_quotReduceRec___redArg___closed__0_once, _init_l_Lean_Kernel_quotReduceRec___redArg___closed__0);
v_nargs_497_ = l_Lean_Expr_getAppNumArgs(v_e_488_);
lean_inc(v_nargs_497_);
v___x_498_ = lean_mk_array(v_nargs_497_, v_dummy_496_);
v___x_499_ = lean_unsigned_to_nat(1u);
v___x_500_ = lean_nat_sub(v_nargs_497_, v___x_499_);
lean_dec(v_nargs_497_);
v_args_501_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_488_, v___x_498_, v___x_500_);
v___x_502_ = lean_array_get_size(v_args_501_);
v___x_503_ = lean_nat_dec_lt(v_mkPos_494_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec_ref(v_args_501_);
lean_dec(v_argPos_495_);
lean_dec(v_mkPos_494_);
lean_dec(v_toBind_491_);
lean_dec(v_whnf_489_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_apply_2(v_toPure_492_, lean_box(0), v___x_504_);
return v___x_505_;
}
else
{
lean_object* v___f_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
lean_inc(v_mkPos_494_);
lean_inc_ref(v_args_501_);
v___f_506_ = lean_alloc_closure((void*)(l_Lean_Kernel_quotReduceRec___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_506_, 0, v_toPure_492_);
lean_closure_set(v___f_506_, 1, v_args_501_);
lean_closure_set(v___f_506_, 2, v_argPos_495_);
lean_closure_set(v___f_506_, 3, v_mkPos_494_);
lean_closure_set(v___f_506_, 4, v___x_499_);
lean_closure_set(v___f_506_, 5, v___x_502_);
v___x_507_ = lean_array_fget(v_args_501_, v_mkPos_494_);
lean_dec(v_mkPos_494_);
lean_dec_ref(v_args_501_);
v___x_508_ = lean_apply_1(v_whnf_489_, v___x_507_);
v___x_509_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_508_, v___f_506_);
return v___x_509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_quotReduceRec(lean_object* v_m_524_, lean_object* v_inst_525_, lean_object* v_e_526_, lean_object* v_whnf_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l_Lean_Kernel_quotReduceRec___redArg(v_inst_525_, v_e_526_, v_whnf_527_);
return v___x_528_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Instantiate(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_LocalContext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Quot(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Instantiate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Quot(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Expr(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Instantiate(uint8_t builtin);
lean_object* initialize_Lean_Kernel_LocalContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Quot(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Instantiate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Quot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Quot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Quot(builtin);
}
#ifdef __cplusplus
}
#endif
