// Lean compiler output
// Module: Lean.Kernel.Environment
// Imports: public import Lean.Kernel.TypeChecker public import Lean.Kernel.Quot public import Lean.Kernel.Inductive.Add public import Lean.Kernel.Primitive
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
lean_object* l_Lean4Lean_Environment_checkPrimitiveDef___redArg(lean_object*);
lean_object* l_Lean_Kernel_Environment_checkName(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Kernel_Environment_checkDuplicatedUnivParams(lean_object*);
lean_object* l_Lean_Kernel_Environment_checkNoMVarNoFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_checkType(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_ensureSort(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_isDefEq(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_environment_add(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_TypeChecker_M_run___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_Environment_addQuot(lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
lean_object* l_Lean4Lean_Environment_checkPrimitiveInductive(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean4Lean_Environment_addInductive(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_checkConstantVal(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_checkConstantVal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean4Lean_addAxiom___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_addAxiom___closed__0;
static lean_once_cell_t l_Lean4Lean_addAxiom___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_addAxiom___closed__1;
static lean_once_cell_t l_Lean4Lean_addAxiom___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_addAxiom___closed__2;
static lean_once_cell_t l_Lean4Lean_addAxiom___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_addAxiom___closed__3;
static lean_once_cell_t l_Lean4Lean_addAxiom___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean4Lean_addAxiom___closed__4;
LEAN_EXPORT lean_object* l_Lean4Lean_addAxiom(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_addAxiom___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "invalid mutual definition, declarations must have the same safety annotation"};
static const lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__0_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__0_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__1 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__1_value;
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__1_value)}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__2 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean4Lean_addMutual___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 71, .m_capacity = 71, .m_length = 70, .m_data = "invalid mutual definition, declaration is not tagged as unsafe/partial"};
static const lean_object* l_Lean4Lean_addMutual___closed__0 = (const lean_object*)&l_Lean4Lean_addMutual___closed__0_value;
static const lean_ctor_object l_Lean4Lean_addMutual___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_addMutual___closed__0_value)}};
static const lean_object* l_Lean4Lean_addMutual___closed__1 = (const lean_object*)&l_Lean4Lean_addMutual___closed__1_value;
static const lean_ctor_object l_Lean4Lean_addMutual___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_addMutual___closed__1_value)}};
static const lean_object* l_Lean4Lean_addMutual___closed__2 = (const lean_object*)&l_Lean4Lean_addMutual___closed__2_value;
static const lean_string_object l_Lean4Lean_addMutual___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid empty mutual definition"};
static const lean_object* l_Lean4Lean_addMutual___closed__3 = (const lean_object*)&l_Lean4Lean_addMutual___closed__3_value;
static const lean_ctor_object l_Lean4Lean_addMutual___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 12}, .m_objs = {((lean_object*)&l_Lean4Lean_addMutual___closed__3_value)}};
static const lean_object* l_Lean4Lean_addMutual___closed__4 = (const lean_object*)&l_Lean4Lean_addMutual___closed__4_value;
static const lean_ctor_object l_Lean4Lean_addMutual___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean4Lean_addMutual___closed__4_value)}};
static const lean_object* l_Lean4Lean_addMutual___closed__5 = (const lean_object*)&l_Lean4Lean_addMutual___closed__5_value;
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_addDecl(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_addDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_addDecl(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Kernel_addDecl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_addDeclImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_kernel_add_decl_impl(lean_object*, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_addDeclImpl___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_kernel_add_decl_without_checking_impl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_checkConstantVal(lean_object* v_env_1_, lean_object* v_v_2_, uint8_t v_allowPrimitive_3_, lean_object* v_a_4_, lean_object* v_a_5_){
_start:
{
lean_object* v_name_6_; lean_object* v_levelParams_7_; lean_object* v_type_8_; lean_object* v___x_9_; 
v_name_6_ = lean_ctor_get(v_v_2_, 0);
lean_inc_n(v_name_6_, 2);
v_levelParams_7_ = lean_ctor_get(v_v_2_, 1);
lean_inc(v_levelParams_7_);
v_type_8_ = lean_ctor_get(v_v_2_, 2);
lean_inc_ref(v_type_8_);
lean_dec_ref(v_v_2_);
lean_inc_ref(v_env_1_);
v___x_9_ = l_Lean_Kernel_Environment_checkName(v_env_1_, v_name_6_, v_allowPrimitive_3_);
if (lean_obj_tag(v___x_9_) == 0)
{
lean_object* v_a_10_; lean_object* v___x_12_; uint8_t v_isShared_13_; uint8_t v_isSharedCheck_17_; 
lean_dec_ref(v_type_8_);
lean_dec(v_levelParams_7_);
lean_dec(v_name_6_);
lean_dec_ref(v_a_5_);
lean_dec_ref(v_env_1_);
v_a_10_ = lean_ctor_get(v___x_9_, 0);
v_isSharedCheck_17_ = !lean_is_exclusive(v___x_9_);
if (v_isSharedCheck_17_ == 0)
{
v___x_12_ = v___x_9_;
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
else
{
lean_inc(v_a_10_);
lean_dec(v___x_9_);
v___x_12_ = lean_box(0);
v_isShared_13_ = v_isSharedCheck_17_;
goto v_resetjp_11_;
}
v_resetjp_11_:
{
lean_object* v___x_15_; 
if (v_isShared_13_ == 0)
{
v___x_15_ = v___x_12_;
goto v_reusejp_14_;
}
else
{
lean_object* v_reuseFailAlloc_16_; 
v_reuseFailAlloc_16_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_16_, 0, v_a_10_);
v___x_15_ = v_reuseFailAlloc_16_;
goto v_reusejp_14_;
}
v_reusejp_14_:
{
return v___x_15_;
}
}
}
else
{
lean_object* v___x_18_; 
lean_dec_ref(v___x_9_);
v___x_18_ = l_Lean_Kernel_Environment_checkDuplicatedUnivParams(v_levelParams_7_);
if (lean_obj_tag(v___x_18_) == 0)
{
lean_object* v_a_19_; lean_object* v___x_21_; uint8_t v_isShared_22_; uint8_t v_isSharedCheck_26_; 
lean_dec_ref(v_type_8_);
lean_dec(v_name_6_);
lean_dec_ref(v_a_5_);
lean_dec_ref(v_env_1_);
v_a_19_ = lean_ctor_get(v___x_18_, 0);
v_isSharedCheck_26_ = !lean_is_exclusive(v___x_18_);
if (v_isSharedCheck_26_ == 0)
{
v___x_21_ = v___x_18_;
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
else
{
lean_inc(v_a_19_);
lean_dec(v___x_18_);
v___x_21_ = lean_box(0);
v_isShared_22_ = v_isSharedCheck_26_;
goto v_resetjp_20_;
}
v_resetjp_20_:
{
lean_object* v___x_24_; 
if (v_isShared_22_ == 0)
{
v___x_24_ = v___x_21_;
goto v_reusejp_23_;
}
else
{
lean_object* v_reuseFailAlloc_25_; 
v_reuseFailAlloc_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_25_, 0, v_a_19_);
v___x_24_ = v_reuseFailAlloc_25_;
goto v_reusejp_23_;
}
v_reusejp_23_:
{
return v___x_24_;
}
}
}
else
{
lean_object* v___x_27_; 
lean_dec_ref(v___x_18_);
lean_inc_ref(v_type_8_);
v___x_27_ = l_Lean_Kernel_Environment_checkNoMVarNoFVar(v_env_1_, v_name_6_, v_type_8_);
if (lean_obj_tag(v___x_27_) == 0)
{
lean_object* v_a_28_; lean_object* v___x_30_; uint8_t v_isShared_31_; uint8_t v_isSharedCheck_35_; 
lean_dec_ref(v_type_8_);
lean_dec_ref(v_a_5_);
v_a_28_ = lean_ctor_get(v___x_27_, 0);
v_isSharedCheck_35_ = !lean_is_exclusive(v___x_27_);
if (v_isSharedCheck_35_ == 0)
{
v___x_30_ = v___x_27_;
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
else
{
lean_inc(v_a_28_);
lean_dec(v___x_27_);
v___x_30_ = lean_box(0);
v_isShared_31_ = v_isSharedCheck_35_;
goto v_resetjp_29_;
}
v_resetjp_29_:
{
lean_object* v___x_33_; 
if (v_isShared_31_ == 0)
{
v___x_33_ = v___x_30_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_28_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
else
{
lean_object* v___x_36_; 
lean_dec_ref(v___x_27_);
lean_inc_ref(v_type_8_);
v___x_36_ = l_Lean_Kernel_TypeChecker_checkType(v_type_8_, v_a_4_, v_a_5_);
if (lean_obj_tag(v___x_36_) == 0)
{
lean_object* v_a_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_44_; 
lean_dec_ref(v_type_8_);
v_a_37_ = lean_ctor_get(v___x_36_, 0);
v_isSharedCheck_44_ = !lean_is_exclusive(v___x_36_);
if (v_isSharedCheck_44_ == 0)
{
v___x_39_ = v___x_36_;
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_a_37_);
lean_dec(v___x_36_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_44_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_42_; 
if (v_isShared_40_ == 0)
{
v___x_42_ = v___x_39_;
goto v_reusejp_41_;
}
else
{
lean_object* v_reuseFailAlloc_43_; 
v_reuseFailAlloc_43_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_43_, 0, v_a_37_);
v___x_42_ = v_reuseFailAlloc_43_;
goto v_reusejp_41_;
}
v_reusejp_41_:
{
return v___x_42_;
}
}
}
else
{
lean_object* v_a_45_; lean_object* v_fst_46_; lean_object* v_snd_47_; lean_object* v___x_48_; 
v_a_45_ = lean_ctor_get(v___x_36_, 0);
lean_inc(v_a_45_);
lean_dec_ref(v___x_36_);
v_fst_46_ = lean_ctor_get(v_a_45_, 0);
lean_inc(v_fst_46_);
v_snd_47_ = lean_ctor_get(v_a_45_, 1);
lean_inc(v_snd_47_);
lean_dec(v_a_45_);
v___x_48_ = l_Lean_Kernel_TypeChecker_ensureSort(v_fst_46_, v_type_8_, v_a_4_, v_snd_47_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v_a_49_; lean_object* v___x_51_; uint8_t v_isShared_52_; uint8_t v_isSharedCheck_56_; 
v_a_49_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_56_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_56_ == 0)
{
v___x_51_ = v___x_48_;
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
else
{
lean_inc(v_a_49_);
lean_dec(v___x_48_);
v___x_51_ = lean_box(0);
v_isShared_52_ = v_isSharedCheck_56_;
goto v_resetjp_50_;
}
v_resetjp_50_:
{
lean_object* v___x_54_; 
if (v_isShared_52_ == 0)
{
v___x_54_ = v___x_51_;
goto v_reusejp_53_;
}
else
{
lean_object* v_reuseFailAlloc_55_; 
v_reuseFailAlloc_55_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_55_, 0, v_a_49_);
v___x_54_ = v_reuseFailAlloc_55_;
goto v_reusejp_53_;
}
v_reusejp_53_:
{
return v___x_54_;
}
}
}
else
{
lean_object* v_a_57_; lean_object* v___x_59_; uint8_t v_isShared_60_; uint8_t v_isSharedCheck_74_; 
v_a_57_ = lean_ctor_get(v___x_48_, 0);
v_isSharedCheck_74_ = !lean_is_exclusive(v___x_48_);
if (v_isSharedCheck_74_ == 0)
{
v___x_59_ = v___x_48_;
v_isShared_60_ = v_isSharedCheck_74_;
goto v_resetjp_58_;
}
else
{
lean_inc(v_a_57_);
lean_dec(v___x_48_);
v___x_59_ = lean_box(0);
v_isShared_60_ = v_isSharedCheck_74_;
goto v_resetjp_58_;
}
v_resetjp_58_:
{
lean_object* v_snd_61_; lean_object* v___x_63_; uint8_t v_isShared_64_; uint8_t v_isSharedCheck_72_; 
v_snd_61_ = lean_ctor_get(v_a_57_, 1);
v_isSharedCheck_72_ = !lean_is_exclusive(v_a_57_);
if (v_isSharedCheck_72_ == 0)
{
lean_object* v_unused_73_; 
v_unused_73_ = lean_ctor_get(v_a_57_, 0);
lean_dec(v_unused_73_);
v___x_63_ = v_a_57_;
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
else
{
lean_inc(v_snd_61_);
lean_dec(v_a_57_);
v___x_63_ = lean_box(0);
v_isShared_64_ = v_isSharedCheck_72_;
goto v_resetjp_62_;
}
v_resetjp_62_:
{
lean_object* v___x_65_; lean_object* v___x_67_; 
v___x_65_ = lean_box(0);
if (v_isShared_64_ == 0)
{
lean_ctor_set(v___x_63_, 0, v___x_65_);
v___x_67_ = v___x_63_;
goto v_reusejp_66_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_65_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_snd_61_);
v___x_67_ = v_reuseFailAlloc_71_;
goto v_reusejp_66_;
}
v_reusejp_66_:
{
lean_object* v___x_69_; 
if (v_isShared_60_ == 0)
{
lean_ctor_set(v___x_59_, 0, v___x_67_);
v___x_69_ = v___x_59_;
goto v_reusejp_68_;
}
else
{
lean_object* v_reuseFailAlloc_70_; 
v_reuseFailAlloc_70_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_70_, 0, v___x_67_);
v___x_69_ = v_reuseFailAlloc_70_;
goto v_reusejp_68_;
}
v_reusejp_68_:
{
return v___x_69_;
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
LEAN_EXPORT lean_object* l_Lean4Lean_checkConstantVal___boxed(lean_object* v_env_75_, lean_object* v_v_76_, lean_object* v_allowPrimitive_77_, lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
uint8_t v_allowPrimitive_boxed_80_; lean_object* v_res_81_; 
v_allowPrimitive_boxed_80_ = lean_unbox(v_allowPrimitive_77_);
v_res_81_ = l_Lean4Lean_checkConstantVal(v_env_75_, v_v_76_, v_allowPrimitive_boxed_80_, v_a_78_, v_a_79_);
lean_dec_ref(v_a_78_);
return v_res_81_;
}
}
static lean_object* _init_l_Lean4Lean_addAxiom___closed__0(void){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; 
v___x_82_ = lean_unsigned_to_nat(32u);
v___x_83_ = lean_mk_empty_array_with_capacity(v___x_82_);
v___x_84_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_84_, 0, v___x_83_);
return v___x_84_;
}
}
static lean_object* _init_l_Lean4Lean_addAxiom___closed__1(void){
_start:
{
size_t v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_85_ = ((size_t)5ULL);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_unsigned_to_nat(32u);
v___x_88_ = lean_mk_empty_array_with_capacity(v___x_87_);
v___x_89_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__0, &l_Lean4Lean_addAxiom___closed__0_once, _init_l_Lean4Lean_addAxiom___closed__0);
v___x_90_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_90_, 0, v___x_89_);
lean_ctor_set(v___x_90_, 1, v___x_88_);
lean_ctor_set(v___x_90_, 2, v___x_86_);
lean_ctor_set(v___x_90_, 3, v___x_86_);
lean_ctor_set_usize(v___x_90_, 4, v___x_85_);
return v___x_90_;
}
}
static lean_object* _init_l_Lean4Lean_addAxiom___closed__2(void){
_start:
{
lean_object* v___x_91_; 
v___x_91_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_91_;
}
}
static lean_object* _init_l_Lean4Lean_addAxiom___closed__3(void){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_92_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__2, &l_Lean4Lean_addAxiom___closed__2_once, _init_l_Lean4Lean_addAxiom___closed__2);
v___x_93_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_93_, 0, v___x_92_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean4Lean_addAxiom___closed__4(void){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_94_ = lean_box(1);
v___x_95_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__1, &l_Lean4Lean_addAxiom___closed__1_once, _init_l_Lean4Lean_addAxiom___closed__1);
v___x_96_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__3, &l_Lean4Lean_addAxiom___closed__3_once, _init_l_Lean4Lean_addAxiom___closed__3);
v___x_97_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v___x_95_);
lean_ctor_set(v___x_97_, 2, v___x_94_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addAxiom(lean_object* v_env_98_, lean_object* v_v_99_, uint8_t v_check_100_){
_start:
{
if (v_check_100_ == 0)
{
goto v___jp_101_;
}
else
{
lean_object* v_toConstantVal_105_; uint8_t v_isUnsafe_106_; uint8_t v___y_108_; 
v_toConstantVal_105_ = lean_ctor_get(v_v_99_, 0);
v_isUnsafe_106_ = lean_ctor_get_uint8(v_v_99_, sizeof(void*)*1);
if (v_isUnsafe_106_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = 1;
v___y_108_ = v___x_123_;
goto v___jp_107_;
}
else
{
uint8_t v___x_124_; 
v___x_124_ = 0;
v___y_108_ = v___x_124_;
goto v___jp_107_;
}
v___jp_107_:
{
lean_object* v_levelParams_109_; lean_object* v___x_110_; uint8_t v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_levelParams_109_ = lean_ctor_get(v_toConstantVal_105_, 1);
v___x_110_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
v___x_111_ = 0;
v___x_112_ = lean_box(v___x_111_);
lean_inc_ref(v_toConstantVal_105_);
lean_inc_ref_n(v_env_98_, 2);
v___x_113_ = lean_alloc_closure((void*)(l_Lean4Lean_checkConstantVal___boxed), 5, 3);
lean_closure_set(v___x_113_, 0, v_env_98_);
lean_closure_set(v___x_113_, 1, v_toConstantVal_105_);
lean_closure_set(v___x_113_, 2, v___x_112_);
lean_inc(v_levelParams_109_);
v___x_114_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_98_, v___y_108_, v___x_110_, v_levelParams_109_, v___x_113_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_122_; 
lean_dec_ref(v_v_99_);
lean_dec_ref(v_env_98_);
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_122_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_122_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_122_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_120_; 
if (v_isShared_118_ == 0)
{
v___x_120_ = v___x_117_;
goto v_reusejp_119_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_a_115_);
v___x_120_ = v_reuseFailAlloc_121_;
goto v_reusejp_119_;
}
v_reusejp_119_:
{
return v___x_120_;
}
}
}
else
{
lean_dec_ref(v___x_114_);
goto v___jp_101_;
}
}
}
v___jp_101_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v_v_99_);
v___x_103_ = lean_environment_add(v_env_98_, v___x_102_);
v___x_104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addAxiom___boxed(lean_object* v_env_125_, lean_object* v_v_126_, lean_object* v_check_127_){
_start:
{
uint8_t v_check_boxed_128_; lean_object* v_res_129_; 
v_check_boxed_128_ = lean_unbox(v_check_127_);
v_res_129_ = l_Lean4Lean_addAxiom(v_env_125_, v_v_126_, v_check_boxed_128_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__0(lean_object* v_value_130_, lean_object* v_type_131_, lean_object* v_v_132_, lean_object* v_env_x27_133_, lean_object* v___y_134_, lean_object* v___y_135_){
_start:
{
lean_object* v___x_136_; 
v___x_136_ = l_Lean_Kernel_TypeChecker_checkType(v_value_130_, v___y_134_, v___y_135_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec_ref(v_env_x27_133_);
lean_dec_ref(v_v_132_);
lean_dec_ref(v_type_131_);
v_a_137_ = lean_ctor_get(v___x_136_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_136_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_136_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
else
{
lean_object* v_a_145_; lean_object* v_fst_146_; lean_object* v_snd_147_; lean_object* v___x_148_; 
v_a_145_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_145_);
lean_dec_ref(v___x_136_);
v_fst_146_ = lean_ctor_get(v_a_145_, 0);
lean_inc_n(v_fst_146_, 2);
v_snd_147_ = lean_ctor_get(v_a_145_, 1);
lean_inc(v_snd_147_);
lean_dec(v_a_145_);
v___x_148_ = l_Lean_Kernel_TypeChecker_isDefEq(v_fst_146_, v_type_131_, v___y_134_, v_snd_147_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_156_; 
lean_dec(v_fst_146_);
lean_dec_ref(v_env_x27_133_);
lean_dec_ref(v_v_132_);
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_156_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_156_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_156_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_154_; 
if (v_isShared_152_ == 0)
{
v___x_154_ = v___x_151_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v_a_149_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
else
{
lean_object* v_a_157_; lean_object* v___x_159_; uint8_t v_isShared_160_; uint8_t v_isSharedCheck_181_; 
v_a_157_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_181_ == 0)
{
v___x_159_ = v___x_148_;
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
else
{
lean_inc(v_a_157_);
lean_dec(v___x_148_);
v___x_159_ = lean_box(0);
v_isShared_160_ = v_isSharedCheck_181_;
goto v_resetjp_158_;
}
v_resetjp_158_:
{
lean_object* v_fst_161_; uint8_t v___x_162_; 
v_fst_161_ = lean_ctor_get(v_a_157_, 0);
v___x_162_ = lean_unbox(v_fst_161_);
if (v___x_162_ == 0)
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
lean_dec(v_a_157_);
v___x_163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_163_, 0, v_v_132_);
v___x_164_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_164_, 0, v_env_x27_133_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
lean_ctor_set(v___x_164_, 2, v_fst_146_);
if (v_isShared_160_ == 0)
{
lean_ctor_set_tag(v___x_159_, 0);
lean_ctor_set(v___x_159_, 0, v___x_164_);
v___x_166_ = v___x_159_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
else
{
lean_object* v_snd_168_; lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_fst_146_);
lean_dec_ref(v_env_x27_133_);
lean_dec_ref(v_v_132_);
v_snd_168_ = lean_ctor_get(v_a_157_, 1);
v_isSharedCheck_179_ = !lean_is_exclusive(v_a_157_);
if (v_isSharedCheck_179_ == 0)
{
lean_object* v_unused_180_; 
v_unused_180_ = lean_ctor_get(v_a_157_, 0);
lean_dec(v_unused_180_);
v___x_170_ = v_a_157_;
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
else
{
lean_inc(v_snd_168_);
lean_dec(v_a_157_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_179_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_box(0);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_172_);
v___x_174_ = v___x_170_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_172_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_snd_168_);
v___x_174_ = v_reuseFailAlloc_178_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
lean_object* v___x_176_; 
if (v_isShared_160_ == 0)
{
lean_ctor_set(v___x_159_, 0, v___x_174_);
v___x_176_ = v___x_159_;
goto v_reusejp_175_;
}
else
{
lean_object* v_reuseFailAlloc_177_; 
v_reuseFailAlloc_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_177_, 0, v___x_174_);
v___x_176_ = v_reuseFailAlloc_177_;
goto v_reusejp_175_;
}
v_reusejp_175_:
{
return v___x_176_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__0___boxed(lean_object* v_value_182_, lean_object* v_type_183_, lean_object* v_v_184_, lean_object* v_env_x27_185_, lean_object* v___y_186_, lean_object* v___y_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_Lean4Lean_addDefinition___lam__0(v_value_182_, v_type_183_, v_v_184_, v_env_x27_185_, v___y_186_, v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__1(lean_object* v_env_189_, lean_object* v_toConstantVal_190_, lean_object* v_value_191_, lean_object* v_type_192_, lean_object* v_v_193_, lean_object* v___y_194_, lean_object* v___y_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_Lean4Lean_Environment_checkPrimitiveDef___redArg(v___y_195_);
if (lean_obj_tag(v___x_196_) == 0)
{
lean_object* v_a_197_; lean_object* v___x_199_; uint8_t v_isShared_200_; uint8_t v_isSharedCheck_204_; 
lean_dec_ref(v_v_193_);
lean_dec_ref(v_type_192_);
lean_dec_ref(v_value_191_);
lean_dec_ref(v_toConstantVal_190_);
lean_dec_ref(v_env_189_);
v_a_197_ = lean_ctor_get(v___x_196_, 0);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_196_);
if (v_isSharedCheck_204_ == 0)
{
v___x_199_ = v___x_196_;
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
else
{
lean_inc(v_a_197_);
lean_dec(v___x_196_);
v___x_199_ = lean_box(0);
v_isShared_200_ = v_isSharedCheck_204_;
goto v_resetjp_198_;
}
v_resetjp_198_:
{
lean_object* v___x_202_; 
if (v_isShared_200_ == 0)
{
v___x_202_ = v___x_199_;
goto v_reusejp_201_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
v___x_202_ = v_reuseFailAlloc_203_;
goto v_reusejp_201_;
}
v_reusejp_201_:
{
return v___x_202_;
}
}
}
else
{
lean_object* v_a_205_; lean_object* v_fst_206_; lean_object* v_snd_207_; uint8_t v___x_208_; lean_object* v___x_209_; 
v_a_205_ = lean_ctor_get(v___x_196_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v___x_196_);
v_fst_206_ = lean_ctor_get(v_a_205_, 0);
lean_inc(v_fst_206_);
v_snd_207_ = lean_ctor_get(v_a_205_, 1);
lean_inc(v_snd_207_);
lean_dec(v_a_205_);
v___x_208_ = lean_unbox(v_fst_206_);
lean_dec(v_fst_206_);
lean_inc_ref(v_env_189_);
v___x_209_ = l_Lean4Lean_checkConstantVal(v_env_189_, v_toConstantVal_190_, v___x_208_, v___y_194_, v_snd_207_);
if (lean_obj_tag(v___x_209_) == 0)
{
lean_dec_ref(v_v_193_);
lean_dec_ref(v_type_192_);
lean_dec_ref(v_value_191_);
lean_dec_ref(v_env_189_);
return v___x_209_;
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_263_; 
v_a_210_ = lean_ctor_get(v___x_209_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_209_);
if (v_isSharedCheck_263_ == 0)
{
v___x_212_ = v___x_209_;
v_isShared_213_ = v_isSharedCheck_263_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_209_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_263_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v_snd_214_; lean_object* v___x_215_; 
v_snd_214_ = lean_ctor_get(v_a_210_, 1);
lean_inc(v_snd_214_);
lean_dec(v_a_210_);
v___x_215_ = l_Lean_Kernel_TypeChecker_checkType(v_value_191_, v___y_194_, v_snd_214_);
if (lean_obj_tag(v___x_215_) == 0)
{
lean_object* v_a_216_; lean_object* v___x_218_; uint8_t v_isShared_219_; uint8_t v_isSharedCheck_223_; 
lean_del_object(v___x_212_);
lean_dec_ref(v_v_193_);
lean_dec_ref(v_type_192_);
lean_dec_ref(v_env_189_);
v_a_216_ = lean_ctor_get(v___x_215_, 0);
v_isSharedCheck_223_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_223_ == 0)
{
v___x_218_ = v___x_215_;
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
else
{
lean_inc(v_a_216_);
lean_dec(v___x_215_);
v___x_218_ = lean_box(0);
v_isShared_219_ = v_isSharedCheck_223_;
goto v_resetjp_217_;
}
v_resetjp_217_:
{
lean_object* v___x_221_; 
if (v_isShared_219_ == 0)
{
v___x_221_ = v___x_218_;
goto v_reusejp_220_;
}
else
{
lean_object* v_reuseFailAlloc_222_; 
v_reuseFailAlloc_222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_222_, 0, v_a_216_);
v___x_221_ = v_reuseFailAlloc_222_;
goto v_reusejp_220_;
}
v_reusejp_220_:
{
return v___x_221_;
}
}
}
else
{
lean_object* v_a_224_; lean_object* v_fst_225_; lean_object* v_snd_226_; lean_object* v___x_227_; 
v_a_224_ = lean_ctor_get(v___x_215_, 0);
lean_inc(v_a_224_);
lean_dec_ref(v___x_215_);
v_fst_225_ = lean_ctor_get(v_a_224_, 0);
lean_inc_n(v_fst_225_, 2);
v_snd_226_ = lean_ctor_get(v_a_224_, 1);
lean_inc(v_snd_226_);
lean_dec(v_a_224_);
v___x_227_ = l_Lean_Kernel_TypeChecker_isDefEq(v_fst_225_, v_type_192_, v___y_194_, v_snd_226_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_230_; uint8_t v_isShared_231_; uint8_t v_isSharedCheck_235_; 
lean_dec(v_fst_225_);
lean_del_object(v___x_212_);
lean_dec_ref(v_v_193_);
lean_dec_ref(v_env_189_);
v_a_228_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_235_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_235_ == 0)
{
v___x_230_ = v___x_227_;
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
else
{
lean_inc(v_a_228_);
lean_dec(v___x_227_);
v___x_230_ = lean_box(0);
v_isShared_231_ = v_isSharedCheck_235_;
goto v_resetjp_229_;
}
v_resetjp_229_:
{
lean_object* v___x_233_; 
if (v_isShared_231_ == 0)
{
v___x_233_ = v___x_230_;
goto v_reusejp_232_;
}
else
{
lean_object* v_reuseFailAlloc_234_; 
v_reuseFailAlloc_234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_234_, 0, v_a_228_);
v___x_233_ = v_reuseFailAlloc_234_;
goto v_reusejp_232_;
}
v_reusejp_232_:
{
return v___x_233_;
}
}
}
else
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_262_; 
v_a_236_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_262_ == 0)
{
v___x_238_ = v___x_227_;
v_isShared_239_ = v_isSharedCheck_262_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_227_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_262_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v_fst_240_; uint8_t v___x_241_; 
v_fst_240_ = lean_ctor_get(v_a_236_, 0);
v___x_241_ = lean_unbox(v_fst_240_);
if (v___x_241_ == 0)
{
lean_object* v___x_243_; 
lean_dec(v_a_236_);
if (v_isShared_213_ == 0)
{
lean_ctor_set(v___x_212_, 0, v_v_193_);
v___x_243_ = v___x_212_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_v_193_);
v___x_243_ = v_reuseFailAlloc_248_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
lean_object* v___x_244_; lean_object* v___x_246_; 
v___x_244_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_244_, 0, v_env_189_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
lean_ctor_set(v___x_244_, 2, v_fst_225_);
if (v_isShared_239_ == 0)
{
lean_ctor_set_tag(v___x_238_, 0);
lean_ctor_set(v___x_238_, 0, v___x_244_);
v___x_246_ = v___x_238_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v___x_244_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
else
{
lean_object* v_snd_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_fst_225_);
lean_del_object(v___x_212_);
lean_dec_ref(v_v_193_);
lean_dec_ref(v_env_189_);
v_snd_249_ = lean_ctor_get(v_a_236_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_a_236_);
if (v_isSharedCheck_260_ == 0)
{
lean_object* v_unused_261_; 
v_unused_261_ = lean_ctor_get(v_a_236_, 0);
lean_dec(v_unused_261_);
v___x_251_ = v_a_236_;
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_snd_249_);
lean_dec(v_a_236_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_260_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_253_ = lean_box(0);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 0, v___x_253_);
v___x_255_ = v___x_251_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v___x_253_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v_snd_249_);
v___x_255_ = v_reuseFailAlloc_259_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
lean_object* v___x_257_; 
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_255_);
v___x_257_ = v___x_238_;
goto v_reusejp_256_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_255_);
v___x_257_ = v_reuseFailAlloc_258_;
goto v_reusejp_256_;
}
v_reusejp_256_:
{
return v___x_257_;
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
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___lam__1___boxed(lean_object* v_env_264_, lean_object* v_toConstantVal_265_, lean_object* v_value_266_, lean_object* v_type_267_, lean_object* v_v_268_, lean_object* v___y_269_, lean_object* v___y_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Lean4Lean_addDefinition___lam__1(v_env_264_, v_toConstantVal_265_, v_value_266_, v_type_267_, v_v_268_, v___y_269_, v___y_270_);
lean_dec_ref(v___y_269_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition(lean_object* v_env_272_, lean_object* v_v_273_, uint8_t v_check_274_){
_start:
{
lean_object* v_toConstantVal_279_; lean_object* v_value_280_; uint8_t v_safety_281_; 
v_toConstantVal_279_ = lean_ctor_get(v_v_273_, 0);
v_value_280_ = lean_ctor_get(v_v_273_, 1);
v_safety_281_ = lean_ctor_get_uint8(v_v_273_, sizeof(void*)*4);
if (v_safety_281_ == 0)
{
lean_inc_ref(v_value_280_);
if (v_check_274_ == 0)
{
goto v___jp_282_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v_levelParams_321_; lean_object* v___x_322_; uint8_t v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_319_ = lean_unsigned_to_nat(32u);
v___x_320_ = lean_mk_empty_array_with_capacity(v___x_319_);
lean_dec_ref(v___x_320_);
v_levelParams_321_ = lean_ctor_get(v_toConstantVal_279_, 1);
v___x_322_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
v___x_323_ = 0;
v___x_324_ = lean_box(v___x_323_);
lean_inc_ref(v_toConstantVal_279_);
lean_inc_ref_n(v_env_272_, 2);
v___x_325_ = lean_alloc_closure((void*)(l_Lean4Lean_checkConstantVal___boxed), 5, 3);
lean_closure_set(v___x_325_, 0, v_env_272_);
lean_closure_set(v___x_325_, 1, v_toConstantVal_279_);
lean_closure_set(v___x_325_, 2, v___x_324_);
lean_inc(v_levelParams_321_);
v___x_326_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_272_, v_safety_281_, v___x_322_, v_levelParams_321_, v___x_325_);
if (lean_obj_tag(v___x_326_) == 0)
{
lean_object* v_a_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_334_; 
lean_dec_ref(v_value_280_);
lean_dec_ref(v_v_273_);
lean_dec_ref(v_env_272_);
v_a_327_ = lean_ctor_get(v___x_326_, 0);
v_isSharedCheck_334_ = !lean_is_exclusive(v___x_326_);
if (v_isSharedCheck_334_ == 0)
{
v___x_329_ = v___x_326_;
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_a_327_);
lean_dec(v___x_326_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_334_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
lean_object* v___x_332_; 
if (v_isShared_330_ == 0)
{
v___x_332_ = v___x_329_;
goto v_reusejp_331_;
}
else
{
lean_object* v_reuseFailAlloc_333_; 
v_reuseFailAlloc_333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_333_, 0, v_a_327_);
v___x_332_ = v_reuseFailAlloc_333_;
goto v_reusejp_331_;
}
v_reusejp_331_:
{
return v___x_332_;
}
}
}
else
{
lean_dec_ref(v___x_326_);
goto v___jp_282_;
}
}
}
else
{
if (v_check_274_ == 0)
{
goto v___jp_275_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_levelParams_337_; lean_object* v_type_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___f_341_; lean_object* v___x_342_; 
v___x_335_ = lean_unsigned_to_nat(32u);
v___x_336_ = lean_mk_empty_array_with_capacity(v___x_335_);
lean_dec_ref(v___x_336_);
v_levelParams_337_ = lean_ctor_get(v_toConstantVal_279_, 1);
v_type_338_ = lean_ctor_get(v_toConstantVal_279_, 2);
v___x_339_ = 1;
v___x_340_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
lean_inc_ref(v_v_273_);
lean_inc_ref(v_type_338_);
lean_inc_ref(v_value_280_);
lean_inc_ref(v_toConstantVal_279_);
lean_inc_ref_n(v_env_272_, 2);
v___f_341_ = lean_alloc_closure((void*)(l_Lean4Lean_addDefinition___lam__1___boxed), 7, 5);
lean_closure_set(v___f_341_, 0, v_env_272_);
lean_closure_set(v___f_341_, 1, v_toConstantVal_279_);
lean_closure_set(v___f_341_, 2, v_value_280_);
lean_closure_set(v___f_341_, 3, v_type_338_);
lean_closure_set(v___f_341_, 4, v_v_273_);
lean_inc(v_levelParams_337_);
v___x_342_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_272_, v___x_339_, v___x_340_, v_levelParams_337_, v___f_341_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_350_; 
lean_dec_ref(v_v_273_);
lean_dec_ref(v_env_272_);
v_a_343_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_350_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_350_ == 0)
{
v___x_345_ = v___x_342_;
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_a_343_);
lean_dec(v___x_342_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_350_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_a_343_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
}
else
{
lean_dec_ref(v___x_342_);
goto v___jp_275_;
}
}
}
v___jp_275_:
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_276_, 0, v_v_273_);
v___x_277_ = lean_environment_add(v_env_272_, v___x_276_);
v___x_278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_278_, 0, v___x_277_);
return v___x_278_;
}
v___jp_282_:
{
lean_object* v___x_283_; lean_object* v_env_x27_284_; 
lean_inc_ref(v_v_273_);
v___x_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_283_, 0, v_v_273_);
v_env_x27_284_ = lean_environment_add(v_env_272_, v___x_283_);
if (v_check_274_ == 0)
{
lean_object* v___x_285_; 
lean_dec_ref(v_value_280_);
lean_dec_ref(v_v_273_);
v___x_285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_285_, 0, v_env_x27_284_);
return v___x_285_;
}
else
{
lean_object* v_name_286_; lean_object* v_levelParams_287_; lean_object* v_type_288_; lean_object* v___x_289_; 
v_name_286_ = lean_ctor_get(v_toConstantVal_279_, 0);
v_levelParams_287_ = lean_ctor_get(v_toConstantVal_279_, 1);
lean_inc(v_levelParams_287_);
v_type_288_ = lean_ctor_get(v_toConstantVal_279_, 2);
lean_inc_ref(v_type_288_);
lean_inc_ref(v_value_280_);
lean_inc(v_name_286_);
lean_inc_ref(v_env_x27_284_);
v___x_289_ = l_Lean_Kernel_Environment_checkNoMVarNoFVar(v_env_x27_284_, v_name_286_, v_value_280_);
if (lean_obj_tag(v___x_289_) == 0)
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
lean_dec_ref(v_type_288_);
lean_dec(v_levelParams_287_);
lean_dec_ref(v_env_x27_284_);
lean_dec_ref(v_value_280_);
lean_dec_ref(v_v_273_);
v_a_290_ = lean_ctor_get(v___x_289_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_289_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_289_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_289_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
else
{
lean_object* v___f_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
lean_dec_ref(v___x_289_);
lean_inc_ref_n(v_env_x27_284_, 2);
v___f_298_ = lean_alloc_closure((void*)(l_Lean4Lean_addDefinition___lam__0___boxed), 6, 4);
lean_closure_set(v___f_298_, 0, v_value_280_);
lean_closure_set(v___f_298_, 1, v_type_288_);
lean_closure_set(v___f_298_, 2, v_v_273_);
lean_closure_set(v___f_298_, 3, v_env_x27_284_);
v___x_299_ = lean_unsigned_to_nat(32u);
v___x_300_ = lean_mk_empty_array_with_capacity(v___x_299_);
lean_dec_ref(v___x_300_);
v___x_301_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
v___x_302_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_x27_284_, v_safety_281_, v___x_301_, v_levelParams_287_, v___f_298_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_310_; 
lean_dec_ref(v_env_x27_284_);
v_a_303_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_310_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_310_ == 0)
{
v___x_305_ = v___x_302_;
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
else
{
lean_inc(v_a_303_);
lean_dec(v___x_302_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_310_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v___x_308_; 
if (v_isShared_306_ == 0)
{
v___x_308_ = v___x_305_;
goto v_reusejp_307_;
}
else
{
lean_object* v_reuseFailAlloc_309_; 
v_reuseFailAlloc_309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_309_, 0, v_a_303_);
v___x_308_ = v_reuseFailAlloc_309_;
goto v_reusejp_307_;
}
v_reusejp_307_:
{
return v___x_308_;
}
}
}
else
{
lean_object* v___x_312_; uint8_t v_isShared_313_; uint8_t v_isSharedCheck_317_; 
v_isSharedCheck_317_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_317_ == 0)
{
lean_object* v_unused_318_; 
v_unused_318_ = lean_ctor_get(v___x_302_, 0);
lean_dec(v_unused_318_);
v___x_312_ = v___x_302_;
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
else
{
lean_dec(v___x_302_);
v___x_312_ = lean_box(0);
v_isShared_313_ = v_isSharedCheck_317_;
goto v_resetjp_311_;
}
v_resetjp_311_:
{
lean_object* v___x_315_; 
if (v_isShared_313_ == 0)
{
lean_ctor_set(v___x_312_, 0, v_env_x27_284_);
v___x_315_ = v___x_312_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_env_x27_284_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
return v___x_315_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addDefinition___boxed(lean_object* v_env_351_, lean_object* v_v_352_, lean_object* v_check_353_){
_start:
{
uint8_t v_check_boxed_354_; lean_object* v_res_355_; 
v_check_boxed_354_ = lean_unbox(v_check_353_);
v_res_355_ = l_Lean4Lean_addDefinition(v_env_351_, v_v_352_, v_check_boxed_354_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem___lam__0(lean_object* v_env_356_, lean_object* v_toConstantVal_357_, uint8_t v___x_358_, lean_object* v_value_359_, lean_object* v_type_360_, lean_object* v_v_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_364_; 
lean_inc_ref(v_env_356_);
v___x_364_ = l_Lean4Lean_checkConstantVal(v_env_356_, v_toConstantVal_357_, v___x_358_, v___y_362_, v___y_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_dec_ref(v_v_361_);
lean_dec_ref(v_type_360_);
lean_dec_ref(v_value_359_);
lean_dec_ref(v_env_356_);
return v___x_364_;
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_418_; 
v_a_365_ = lean_ctor_get(v___x_364_, 0);
v_isSharedCheck_418_ = !lean_is_exclusive(v___x_364_);
if (v_isSharedCheck_418_ == 0)
{
v___x_367_ = v___x_364_;
v_isShared_368_ = v_isSharedCheck_418_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_364_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_418_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v_snd_369_; lean_object* v___x_370_; 
v_snd_369_ = lean_ctor_get(v_a_365_, 1);
lean_inc(v_snd_369_);
lean_dec(v_a_365_);
v___x_370_ = l_Lean_Kernel_TypeChecker_checkType(v_value_359_, v___y_362_, v_snd_369_);
if (lean_obj_tag(v___x_370_) == 0)
{
lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_378_; 
lean_del_object(v___x_367_);
lean_dec_ref(v_v_361_);
lean_dec_ref(v_type_360_);
lean_dec_ref(v_env_356_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_378_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_378_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_378_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_376_; 
if (v_isShared_374_ == 0)
{
v___x_376_ = v___x_373_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v_a_371_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
}
else
{
lean_object* v_a_379_; lean_object* v_fst_380_; lean_object* v_snd_381_; lean_object* v___x_382_; 
v_a_379_ = lean_ctor_get(v___x_370_, 0);
lean_inc(v_a_379_);
lean_dec_ref(v___x_370_);
v_fst_380_ = lean_ctor_get(v_a_379_, 0);
lean_inc_n(v_fst_380_, 2);
v_snd_381_ = lean_ctor_get(v_a_379_, 1);
lean_inc(v_snd_381_);
lean_dec(v_a_379_);
v___x_382_ = l_Lean_Kernel_TypeChecker_isDefEq(v_fst_380_, v_type_360_, v___y_362_, v_snd_381_);
if (lean_obj_tag(v___x_382_) == 0)
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
lean_dec(v_fst_380_);
lean_del_object(v___x_367_);
lean_dec_ref(v_v_361_);
lean_dec_ref(v_env_356_);
v_a_383_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_382_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_382_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_417_; 
v_a_391_ = lean_ctor_get(v___x_382_, 0);
v_isSharedCheck_417_ = !lean_is_exclusive(v___x_382_);
if (v_isSharedCheck_417_ == 0)
{
v___x_393_ = v___x_382_;
v_isShared_394_ = v_isSharedCheck_417_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_382_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_417_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v_fst_395_; uint8_t v___x_396_; 
v_fst_395_ = lean_ctor_get(v_a_391_, 0);
v___x_396_ = lean_unbox(v_fst_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_398_; 
lean_dec(v_a_391_);
if (v_isShared_368_ == 0)
{
lean_ctor_set_tag(v___x_367_, 2);
lean_ctor_set(v___x_367_, 0, v_v_361_);
v___x_398_ = v___x_367_;
goto v_reusejp_397_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_v_361_);
v___x_398_ = v_reuseFailAlloc_403_;
goto v_reusejp_397_;
}
v_reusejp_397_:
{
lean_object* v___x_399_; lean_object* v___x_401_; 
v___x_399_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_399_, 0, v_env_356_);
lean_ctor_set(v___x_399_, 1, v___x_398_);
lean_ctor_set(v___x_399_, 2, v_fst_380_);
if (v_isShared_394_ == 0)
{
lean_ctor_set_tag(v___x_393_, 0);
lean_ctor_set(v___x_393_, 0, v___x_399_);
v___x_401_ = v___x_393_;
goto v_reusejp_400_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_399_);
v___x_401_ = v_reuseFailAlloc_402_;
goto v_reusejp_400_;
}
v_reusejp_400_:
{
return v___x_401_;
}
}
}
else
{
lean_object* v_snd_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_415_; 
lean_dec(v_fst_380_);
lean_del_object(v___x_367_);
lean_dec_ref(v_v_361_);
lean_dec_ref(v_env_356_);
v_snd_404_ = lean_ctor_get(v_a_391_, 1);
v_isSharedCheck_415_ = !lean_is_exclusive(v_a_391_);
if (v_isSharedCheck_415_ == 0)
{
lean_object* v_unused_416_; 
v_unused_416_ = lean_ctor_get(v_a_391_, 0);
lean_dec(v_unused_416_);
v___x_406_ = v_a_391_;
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_snd_404_);
lean_dec(v_a_391_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_415_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
lean_object* v___x_408_; lean_object* v___x_410_; 
v___x_408_ = lean_box(0);
if (v_isShared_407_ == 0)
{
lean_ctor_set(v___x_406_, 0, v___x_408_);
v___x_410_ = v___x_406_;
goto v_reusejp_409_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v___x_408_);
lean_ctor_set(v_reuseFailAlloc_414_, 1, v_snd_404_);
v___x_410_ = v_reuseFailAlloc_414_;
goto v_reusejp_409_;
}
v_reusejp_409_:
{
lean_object* v___x_412_; 
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 0, v___x_410_);
v___x_412_ = v___x_393_;
goto v_reusejp_411_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v___x_410_);
v___x_412_ = v_reuseFailAlloc_413_;
goto v_reusejp_411_;
}
v_reusejp_411_:
{
return v___x_412_;
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
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem___lam__0___boxed(lean_object* v_env_419_, lean_object* v_toConstantVal_420_, lean_object* v___x_421_, lean_object* v_value_422_, lean_object* v_type_423_, lean_object* v_v_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
uint8_t v___x_1664__boxed_427_; lean_object* v_res_428_; 
v___x_1664__boxed_427_ = lean_unbox(v___x_421_);
v_res_428_ = l_Lean4Lean_addTheorem___lam__0(v_env_419_, v_toConstantVal_420_, v___x_1664__boxed_427_, v_value_422_, v_type_423_, v_v_424_, v___y_425_, v___y_426_);
lean_dec_ref(v___y_425_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem(lean_object* v_env_429_, lean_object* v_v_430_, uint8_t v_check_431_){
_start:
{
if (v_check_431_ == 0)
{
goto v___jp_432_;
}
else
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v_toConstantVal_438_; lean_object* v_value_439_; lean_object* v_levelParams_440_; lean_object* v_type_441_; uint8_t v___x_442_; lean_object* v___x_443_; uint8_t v___x_444_; lean_object* v___x_445_; lean_object* v___f_446_; lean_object* v___x_447_; 
v___x_436_ = lean_unsigned_to_nat(32u);
v___x_437_ = lean_mk_empty_array_with_capacity(v___x_436_);
lean_dec_ref(v___x_437_);
v_toConstantVal_438_ = lean_ctor_get(v_v_430_, 0);
v_value_439_ = lean_ctor_get(v_v_430_, 1);
v_levelParams_440_ = lean_ctor_get(v_toConstantVal_438_, 1);
v_type_441_ = lean_ctor_get(v_toConstantVal_438_, 2);
v___x_442_ = 1;
v___x_443_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
v___x_444_ = 0;
v___x_445_ = lean_box(v___x_444_);
lean_inc_ref(v_v_430_);
lean_inc_ref(v_type_441_);
lean_inc_ref(v_value_439_);
lean_inc_ref(v_toConstantVal_438_);
lean_inc_ref_n(v_env_429_, 2);
v___f_446_ = lean_alloc_closure((void*)(l_Lean4Lean_addTheorem___lam__0___boxed), 8, 6);
lean_closure_set(v___f_446_, 0, v_env_429_);
lean_closure_set(v___f_446_, 1, v_toConstantVal_438_);
lean_closure_set(v___f_446_, 2, v___x_445_);
lean_closure_set(v___f_446_, 3, v_value_439_);
lean_closure_set(v___f_446_, 4, v_type_441_);
lean_closure_set(v___f_446_, 5, v_v_430_);
lean_inc(v_levelParams_440_);
v___x_447_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_429_, v___x_442_, v___x_443_, v_levelParams_440_, v___f_446_);
if (lean_obj_tag(v___x_447_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_450_; uint8_t v_isShared_451_; uint8_t v_isSharedCheck_455_; 
lean_dec_ref(v_v_430_);
lean_dec_ref(v_env_429_);
v_a_448_ = lean_ctor_get(v___x_447_, 0);
v_isSharedCheck_455_ = !lean_is_exclusive(v___x_447_);
if (v_isSharedCheck_455_ == 0)
{
v___x_450_ = v___x_447_;
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
else
{
lean_inc(v_a_448_);
lean_dec(v___x_447_);
v___x_450_ = lean_box(0);
v_isShared_451_ = v_isSharedCheck_455_;
goto v_resetjp_449_;
}
v_resetjp_449_:
{
lean_object* v___x_453_; 
if (v_isShared_451_ == 0)
{
v___x_453_ = v___x_450_;
goto v_reusejp_452_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_a_448_);
v___x_453_ = v_reuseFailAlloc_454_;
goto v_reusejp_452_;
}
v_reusejp_452_:
{
return v___x_453_;
}
}
}
else
{
lean_dec_ref(v___x_447_);
goto v___jp_432_;
}
}
v___jp_432_:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_433_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_433_, 0, v_v_430_);
v___x_434_ = lean_environment_add(v_env_429_, v___x_433_);
v___x_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_435_, 0, v___x_434_);
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addTheorem___boxed(lean_object* v_env_456_, lean_object* v_v_457_, lean_object* v_check_458_){
_start:
{
uint8_t v_check_boxed_459_; lean_object* v_res_460_; 
v_check_boxed_459_ = lean_unbox(v_check_458_);
v_res_460_ = l_Lean4Lean_addTheorem(v_env_456_, v_v_457_, v_check_boxed_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque___lam__0(lean_object* v_env_461_, lean_object* v_toConstantVal_462_, uint8_t v___x_463_, lean_object* v_value_464_, lean_object* v_type_465_, lean_object* v_v_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_469_; 
lean_inc_ref(v_env_461_);
v___x_469_ = l_Lean4Lean_checkConstantVal(v_env_461_, v_toConstantVal_462_, v___x_463_, v___y_467_, v___y_468_);
if (lean_obj_tag(v___x_469_) == 0)
{
lean_dec_ref(v_v_466_);
lean_dec_ref(v_type_465_);
lean_dec_ref(v_value_464_);
lean_dec_ref(v_env_461_);
return v___x_469_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_472_; uint8_t v_isShared_473_; uint8_t v_isSharedCheck_523_; 
v_a_470_ = lean_ctor_get(v___x_469_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_469_);
if (v_isSharedCheck_523_ == 0)
{
v___x_472_ = v___x_469_;
v_isShared_473_ = v_isSharedCheck_523_;
goto v_resetjp_471_;
}
else
{
lean_inc(v_a_470_);
lean_dec(v___x_469_);
v___x_472_ = lean_box(0);
v_isShared_473_ = v_isSharedCheck_523_;
goto v_resetjp_471_;
}
v_resetjp_471_:
{
lean_object* v_snd_474_; lean_object* v___x_475_; 
v_snd_474_ = lean_ctor_get(v_a_470_, 1);
lean_inc(v_snd_474_);
lean_dec(v_a_470_);
v___x_475_ = l_Lean_Kernel_TypeChecker_checkType(v_value_464_, v___y_467_, v_snd_474_);
if (lean_obj_tag(v___x_475_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_478_; uint8_t v_isShared_479_; uint8_t v_isSharedCheck_483_; 
lean_del_object(v___x_472_);
lean_dec_ref(v_v_466_);
lean_dec_ref(v_type_465_);
lean_dec_ref(v_env_461_);
v_a_476_ = lean_ctor_get(v___x_475_, 0);
v_isSharedCheck_483_ = !lean_is_exclusive(v___x_475_);
if (v_isSharedCheck_483_ == 0)
{
v___x_478_ = v___x_475_;
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
else
{
lean_inc(v_a_476_);
lean_dec(v___x_475_);
v___x_478_ = lean_box(0);
v_isShared_479_ = v_isSharedCheck_483_;
goto v_resetjp_477_;
}
v_resetjp_477_:
{
lean_object* v___x_481_; 
if (v_isShared_479_ == 0)
{
v___x_481_ = v___x_478_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v_a_476_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
}
else
{
lean_object* v_a_484_; lean_object* v_fst_485_; lean_object* v_snd_486_; lean_object* v___x_487_; 
v_a_484_ = lean_ctor_get(v___x_475_, 0);
lean_inc(v_a_484_);
lean_dec_ref(v___x_475_);
v_fst_485_ = lean_ctor_get(v_a_484_, 0);
lean_inc_n(v_fst_485_, 2);
v_snd_486_ = lean_ctor_get(v_a_484_, 1);
lean_inc(v_snd_486_);
lean_dec(v_a_484_);
v___x_487_ = l_Lean_Kernel_TypeChecker_isDefEq(v_fst_485_, v_type_465_, v___y_467_, v_snd_486_);
if (lean_obj_tag(v___x_487_) == 0)
{
lean_object* v_a_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_495_; 
lean_dec(v_fst_485_);
lean_del_object(v___x_472_);
lean_dec_ref(v_v_466_);
lean_dec_ref(v_env_461_);
v_a_488_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_495_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_495_ == 0)
{
v___x_490_ = v___x_487_;
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_a_488_);
lean_dec(v___x_487_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_495_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_493_; 
if (v_isShared_491_ == 0)
{
v___x_493_ = v___x_490_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v_a_488_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
else
{
lean_object* v_a_496_; lean_object* v___x_498_; uint8_t v_isShared_499_; uint8_t v_isSharedCheck_522_; 
v_a_496_ = lean_ctor_get(v___x_487_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_487_);
if (v_isSharedCheck_522_ == 0)
{
v___x_498_ = v___x_487_;
v_isShared_499_ = v_isSharedCheck_522_;
goto v_resetjp_497_;
}
else
{
lean_inc(v_a_496_);
lean_dec(v___x_487_);
v___x_498_ = lean_box(0);
v_isShared_499_ = v_isSharedCheck_522_;
goto v_resetjp_497_;
}
v_resetjp_497_:
{
lean_object* v_fst_500_; uint8_t v___x_501_; 
v_fst_500_ = lean_ctor_get(v_a_496_, 0);
v___x_501_ = lean_unbox(v_fst_500_);
if (v___x_501_ == 0)
{
lean_object* v___x_503_; 
lean_dec(v_a_496_);
if (v_isShared_473_ == 0)
{
lean_ctor_set_tag(v___x_472_, 3);
lean_ctor_set(v___x_472_, 0, v_v_466_);
v___x_503_ = v___x_472_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_v_466_);
v___x_503_ = v_reuseFailAlloc_508_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
lean_object* v___x_504_; lean_object* v___x_506_; 
v___x_504_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_504_, 0, v_env_461_);
lean_ctor_set(v___x_504_, 1, v___x_503_);
lean_ctor_set(v___x_504_, 2, v_fst_485_);
if (v_isShared_499_ == 0)
{
lean_ctor_set_tag(v___x_498_, 0);
lean_ctor_set(v___x_498_, 0, v___x_504_);
v___x_506_ = v___x_498_;
goto v_reusejp_505_;
}
else
{
lean_object* v_reuseFailAlloc_507_; 
v_reuseFailAlloc_507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_507_, 0, v___x_504_);
v___x_506_ = v_reuseFailAlloc_507_;
goto v_reusejp_505_;
}
v_reusejp_505_:
{
return v___x_506_;
}
}
}
else
{
lean_object* v_snd_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_520_; 
lean_dec(v_fst_485_);
lean_del_object(v___x_472_);
lean_dec_ref(v_v_466_);
lean_dec_ref(v_env_461_);
v_snd_509_ = lean_ctor_get(v_a_496_, 1);
v_isSharedCheck_520_ = !lean_is_exclusive(v_a_496_);
if (v_isSharedCheck_520_ == 0)
{
lean_object* v_unused_521_; 
v_unused_521_ = lean_ctor_get(v_a_496_, 0);
lean_dec(v_unused_521_);
v___x_511_ = v_a_496_;
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_snd_509_);
lean_dec(v_a_496_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_520_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_515_; 
v___x_513_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_513_);
v___x_515_ = v___x_511_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v___x_513_);
lean_ctor_set(v_reuseFailAlloc_519_, 1, v_snd_509_);
v___x_515_ = v_reuseFailAlloc_519_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_517_; 
if (v_isShared_499_ == 0)
{
lean_ctor_set(v___x_498_, 0, v___x_515_);
v___x_517_ = v___x_498_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_518_; 
v_reuseFailAlloc_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_518_, 0, v___x_515_);
v___x_517_ = v_reuseFailAlloc_518_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
return v___x_517_;
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
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque___lam__0___boxed(lean_object* v_env_524_, lean_object* v_toConstantVal_525_, lean_object* v___x_526_, lean_object* v_value_527_, lean_object* v_type_528_, lean_object* v_v_529_, lean_object* v___y_530_, lean_object* v___y_531_){
_start:
{
uint8_t v___x_1664__boxed_532_; lean_object* v_res_533_; 
v___x_1664__boxed_532_ = lean_unbox(v___x_526_);
v_res_533_ = l_Lean4Lean_addOpaque___lam__0(v_env_524_, v_toConstantVal_525_, v___x_1664__boxed_532_, v_value_527_, v_type_528_, v_v_529_, v___y_530_, v___y_531_);
lean_dec_ref(v___y_530_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque(lean_object* v_env_534_, lean_object* v_v_535_, uint8_t v_check_536_){
_start:
{
if (v_check_536_ == 0)
{
goto v___jp_537_;
}
else
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v_toConstantVal_543_; lean_object* v_value_544_; lean_object* v_levelParams_545_; lean_object* v_type_546_; uint8_t v___x_547_; lean_object* v___x_548_; uint8_t v___x_549_; lean_object* v___x_550_; lean_object* v___f_551_; lean_object* v___x_552_; 
v___x_541_ = lean_unsigned_to_nat(32u);
v___x_542_ = lean_mk_empty_array_with_capacity(v___x_541_);
lean_dec_ref(v___x_542_);
v_toConstantVal_543_ = lean_ctor_get(v_v_535_, 0);
v_value_544_ = lean_ctor_get(v_v_535_, 1);
v_levelParams_545_ = lean_ctor_get(v_toConstantVal_543_, 1);
v_type_546_ = lean_ctor_get(v_toConstantVal_543_, 2);
v___x_547_ = 1;
v___x_548_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
v___x_549_ = 0;
v___x_550_ = lean_box(v___x_549_);
lean_inc_ref(v_v_535_);
lean_inc_ref(v_type_546_);
lean_inc_ref(v_value_544_);
lean_inc_ref(v_toConstantVal_543_);
lean_inc_ref_n(v_env_534_, 2);
v___f_551_ = lean_alloc_closure((void*)(l_Lean4Lean_addOpaque___lam__0___boxed), 8, 6);
lean_closure_set(v___f_551_, 0, v_env_534_);
lean_closure_set(v___f_551_, 1, v_toConstantVal_543_);
lean_closure_set(v___f_551_, 2, v___x_550_);
lean_closure_set(v___f_551_, 3, v_value_544_);
lean_closure_set(v___f_551_, 4, v_type_546_);
lean_closure_set(v___f_551_, 5, v_v_535_);
lean_inc(v_levelParams_545_);
v___x_552_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_534_, v___x_547_, v___x_548_, v_levelParams_545_, v___f_551_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v_a_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_560_; 
lean_dec_ref(v_v_535_);
lean_dec_ref(v_env_534_);
v_a_553_ = lean_ctor_get(v___x_552_, 0);
v_isSharedCheck_560_ = !lean_is_exclusive(v___x_552_);
if (v_isSharedCheck_560_ == 0)
{
v___x_555_ = v___x_552_;
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_a_553_);
lean_dec(v___x_552_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_560_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
lean_object* v___x_558_; 
if (v_isShared_556_ == 0)
{
v___x_558_ = v___x_555_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_a_553_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
}
else
{
lean_dec_ref(v___x_552_);
goto v___jp_537_;
}
}
v___jp_537_:
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_538_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_538_, 0, v_v_535_);
v___x_539_ = lean_environment_add(v_env_534_, v___x_538_);
v___x_540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addOpaque___boxed(lean_object* v_env_561_, lean_object* v_v_562_, lean_object* v_check_563_){
_start:
{
uint8_t v_check_boxed_564_; lean_object* v_res_565_; 
v_check_boxed_564_ = lean_unbox(v_check_563_);
v_res_565_ = l_Lean4Lean_addOpaque(v_env_561_, v_v_562_, v_check_boxed_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___redArg(lean_object* v_a_566_, lean_object* v_vs_567_, lean_object* v_as_x27_568_, lean_object* v_b_569_, lean_object* v___y_570_, lean_object* v___y_571_){
_start:
{
if (lean_obj_tag(v_as_x27_568_) == 0)
{
lean_object* v___x_572_; lean_object* v___x_573_; 
lean_dec(v_vs_567_);
lean_dec_ref(v_a_566_);
v___x_572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_572_, 0, v_b_569_);
lean_ctor_set(v___x_572_, 1, v___y_571_);
v___x_573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_573_, 0, v___x_572_);
return v___x_573_;
}
else
{
lean_object* v_head_574_; lean_object* v_toConstantVal_575_; lean_object* v_tail_576_; lean_object* v_value_577_; lean_object* v_name_578_; lean_object* v_type_579_; lean_object* v___x_580_; 
v_head_574_ = lean_ctor_get(v_as_x27_568_, 0);
v_toConstantVal_575_ = lean_ctor_get(v_head_574_, 0);
v_tail_576_ = lean_ctor_get(v_as_x27_568_, 1);
v_value_577_ = lean_ctor_get(v_head_574_, 1);
v_name_578_ = lean_ctor_get(v_toConstantVal_575_, 0);
v_type_579_ = lean_ctor_get(v_toConstantVal_575_, 2);
lean_inc_ref(v_value_577_);
lean_inc(v_name_578_);
lean_inc_ref(v_a_566_);
v___x_580_ = l_Lean_Kernel_Environment_checkNoMVarNoFVar(v_a_566_, v_name_578_, v_value_577_);
if (lean_obj_tag(v___x_580_) == 0)
{
lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_588_; 
lean_dec_ref(v___y_571_);
lean_dec(v_vs_567_);
lean_dec_ref(v_a_566_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_588_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_588_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_588_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_586_; 
if (v_isShared_584_ == 0)
{
v___x_586_ = v___x_583_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_a_581_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
}
else
{
lean_object* v___x_589_; 
lean_dec_ref(v___x_580_);
lean_inc_ref(v_value_577_);
v___x_589_ = l_Lean_Kernel_TypeChecker_checkType(v_value_577_, v___y_570_, v___y_571_);
if (lean_obj_tag(v___x_589_) == 0)
{
lean_object* v_a_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_597_; 
lean_dec(v_vs_567_);
lean_dec_ref(v_a_566_);
v_a_590_ = lean_ctor_get(v___x_589_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_589_);
if (v_isSharedCheck_597_ == 0)
{
v___x_592_ = v___x_589_;
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_a_590_);
lean_dec(v___x_589_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_597_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_595_; 
if (v_isShared_593_ == 0)
{
v___x_595_ = v___x_592_;
goto v_reusejp_594_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_a_590_);
v___x_595_ = v_reuseFailAlloc_596_;
goto v_reusejp_594_;
}
v_reusejp_594_:
{
return v___x_595_;
}
}
}
else
{
lean_object* v_a_598_; lean_object* v_fst_599_; lean_object* v_snd_600_; lean_object* v___x_601_; 
v_a_598_ = lean_ctor_get(v___x_589_, 0);
lean_inc(v_a_598_);
lean_dec_ref(v___x_589_);
v_fst_599_ = lean_ctor_get(v_a_598_, 0);
lean_inc_n(v_fst_599_, 2);
v_snd_600_ = lean_ctor_get(v_a_598_, 1);
lean_inc(v_snd_600_);
lean_dec(v_a_598_);
lean_inc_ref(v_type_579_);
v___x_601_ = l_Lean_Kernel_TypeChecker_isDefEq(v_fst_599_, v_type_579_, v___y_570_, v_snd_600_);
if (lean_obj_tag(v___x_601_) == 0)
{
lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_609_; 
lean_dec(v_fst_599_);
lean_dec(v_vs_567_);
lean_dec_ref(v_a_566_);
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_609_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_609_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_609_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_607_; 
if (v_isShared_605_ == 0)
{
v___x_607_ = v___x_604_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_a_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
}
else
{
lean_object* v_a_610_; lean_object* v___x_612_; uint8_t v_isShared_613_; uint8_t v_isSharedCheck_624_; 
v_a_610_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_624_ == 0)
{
v___x_612_ = v___x_601_;
v_isShared_613_ = v_isSharedCheck_624_;
goto v_resetjp_611_;
}
else
{
lean_inc(v_a_610_);
lean_dec(v___x_601_);
v___x_612_ = lean_box(0);
v_isShared_613_ = v_isSharedCheck_624_;
goto v_resetjp_611_;
}
v_resetjp_611_:
{
lean_object* v_fst_614_; uint8_t v___x_615_; 
v_fst_614_ = lean_ctor_get(v_a_610_, 0);
v___x_615_ = lean_unbox(v_fst_614_);
if (v___x_615_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_619_; 
lean_dec(v_a_610_);
v___x_616_ = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(v___x_616_, 0, v_vs_567_);
v___x_617_ = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(v___x_617_, 0, v_a_566_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
lean_ctor_set(v___x_617_, 2, v_fst_599_);
if (v_isShared_613_ == 0)
{
lean_ctor_set_tag(v___x_612_, 0);
lean_ctor_set(v___x_612_, 0, v___x_617_);
v___x_619_ = v___x_612_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
lean_object* v_snd_621_; lean_object* v___x_622_; 
lean_del_object(v___x_612_);
lean_dec(v_fst_599_);
v_snd_621_ = lean_ctor_get(v_a_610_, 1);
lean_inc(v_snd_621_);
lean_dec(v_a_610_);
v___x_622_ = lean_box(0);
v_as_x27_568_ = v_tail_576_;
v_b_569_ = v___x_622_;
v___y_571_ = v_snd_621_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___redArg___boxed(lean_object* v_a_625_, lean_object* v_vs_626_, lean_object* v_as_x27_627_, lean_object* v_b_628_, lean_object* v___y_629_, lean_object* v___y_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___redArg(v_a_625_, v_vs_626_, v_as_x27_627_, v_b_628_, v___y_629_, v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v_as_x27_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__0(lean_object* v_a_632_, lean_object* v_vs_633_, lean_object* v___x_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_637_; 
lean_inc(v_vs_633_);
v___x_637_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___redArg(v_a_632_, v_vs_633_, v_vs_633_, v___x_634_, v___y_635_, v___y_636_);
lean_dec(v_vs_633_);
if (lean_obj_tag(v___x_637_) == 0)
{
return v___x_637_;
}
else
{
lean_object* v_a_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_654_; 
v_a_638_ = lean_ctor_get(v___x_637_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_637_);
if (v_isSharedCheck_654_ == 0)
{
v___x_640_ = v___x_637_;
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_a_638_);
lean_dec(v___x_637_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_654_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v_snd_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_652_; 
v_snd_642_ = lean_ctor_get(v_a_638_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_a_638_);
if (v_isSharedCheck_652_ == 0)
{
lean_object* v_unused_653_; 
v_unused_653_ = lean_ctor_get(v_a_638_, 0);
lean_dec(v_unused_653_);
v___x_644_ = v_a_638_;
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_snd_642_);
lean_dec(v_a_638_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
lean_object* v___x_647_; 
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 0, v___x_634_);
v___x_647_ = v___x_644_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_snd_642_);
v___x_647_ = v_reuseFailAlloc_651_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v___x_647_);
v___x_649_ = v___x_640_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_647_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__0___boxed(lean_object* v_a_655_, lean_object* v_vs_656_, lean_object* v___x_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean4Lean_addMutual___lam__0(v_a_655_, v_vs_656_, v___x_657_, v___y_658_, v___y_659_);
lean_dec_ref(v___y_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg(uint8_t v___x_666_, lean_object* v_env_667_, lean_object* v_as_x27_668_, lean_object* v_b_669_, lean_object* v___y_670_, lean_object* v___y_671_){
_start:
{
if (lean_obj_tag(v_as_x27_668_) == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; 
lean_dec_ref(v_env_667_);
v___x_672_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_672_, 0, v_b_669_);
lean_ctor_set(v___x_672_, 1, v___y_671_);
v___x_673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
else
{
lean_object* v_head_674_; lean_object* v_tail_675_; lean_object* v_toConstantVal_676_; uint8_t v_safety_677_; uint8_t v___x_678_; 
v_head_674_ = lean_ctor_get(v_as_x27_668_, 0);
v_tail_675_ = lean_ctor_get(v_as_x27_668_, 1);
v_toConstantVal_676_ = lean_ctor_get(v_head_674_, 0);
v_safety_677_ = lean_ctor_get_uint8(v_head_674_, sizeof(void*)*4);
v___x_678_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_677_, v___x_666_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; 
lean_dec_ref(v___y_671_);
lean_dec_ref(v_env_667_);
v___x_679_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___closed__2));
return v___x_679_;
}
else
{
uint8_t v___x_680_; lean_object* v___x_681_; 
v___x_680_ = 0;
lean_inc_ref(v_toConstantVal_676_);
lean_inc_ref(v_env_667_);
v___x_681_ = l_Lean4Lean_checkConstantVal(v_env_667_, v_toConstantVal_676_, v___x_680_, v___y_670_, v___y_671_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_dec_ref(v_env_667_);
return v___x_681_;
}
else
{
lean_object* v_a_682_; lean_object* v_snd_683_; lean_object* v___x_684_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref(v___x_681_);
v_snd_683_ = lean_ctor_get(v_a_682_, 1);
lean_inc(v_snd_683_);
lean_dec(v_a_682_);
v___x_684_ = lean_box(0);
v_as_x27_668_ = v_tail_675_;
v_b_669_ = v___x_684_;
v___y_671_ = v_snd_683_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg___boxed(lean_object* v___x_686_, lean_object* v_env_687_, lean_object* v_as_x27_688_, lean_object* v_b_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v___x_7468__boxed_692_; lean_object* v_res_693_; 
v___x_7468__boxed_692_ = lean_unbox(v___x_686_);
v_res_693_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg(v___x_7468__boxed_692_, v_env_687_, v_as_x27_688_, v_b_689_, v___y_690_, v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v_as_x27_688_);
return v_res_693_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__1(uint8_t v_safety_694_, lean_object* v_env_695_, lean_object* v_vs_696_, lean_object* v___x_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_700_; 
v___x_700_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg(v_safety_694_, v_env_695_, v_vs_696_, v___x_697_, v___y_698_, v___y_699_);
if (lean_obj_tag(v___x_700_) == 0)
{
return v___x_700_;
}
else
{
lean_object* v_a_701_; lean_object* v___x_703_; uint8_t v_isShared_704_; uint8_t v_isSharedCheck_717_; 
v_a_701_ = lean_ctor_get(v___x_700_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_700_);
if (v_isSharedCheck_717_ == 0)
{
v___x_703_ = v___x_700_;
v_isShared_704_ = v_isSharedCheck_717_;
goto v_resetjp_702_;
}
else
{
lean_inc(v_a_701_);
lean_dec(v___x_700_);
v___x_703_ = lean_box(0);
v_isShared_704_ = v_isSharedCheck_717_;
goto v_resetjp_702_;
}
v_resetjp_702_:
{
lean_object* v_snd_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_715_; 
v_snd_705_ = lean_ctor_get(v_a_701_, 1);
v_isSharedCheck_715_ = !lean_is_exclusive(v_a_701_);
if (v_isSharedCheck_715_ == 0)
{
lean_object* v_unused_716_; 
v_unused_716_ = lean_ctor_get(v_a_701_, 0);
lean_dec(v_unused_716_);
v___x_707_ = v_a_701_;
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_snd_705_);
lean_dec(v_a_701_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_715_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v___x_710_; 
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_697_);
v___x_710_ = v___x_707_;
goto v_reusejp_709_;
}
else
{
lean_object* v_reuseFailAlloc_714_; 
v_reuseFailAlloc_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_714_, 1, v_snd_705_);
v___x_710_ = v_reuseFailAlloc_714_;
goto v_reusejp_709_;
}
v_reusejp_709_:
{
lean_object* v___x_712_; 
if (v_isShared_704_ == 0)
{
lean_ctor_set(v___x_703_, 0, v___x_710_);
v___x_712_ = v___x_703_;
goto v_reusejp_711_;
}
else
{
lean_object* v_reuseFailAlloc_713_; 
v_reuseFailAlloc_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_710_);
v___x_712_ = v_reuseFailAlloc_713_;
goto v_reusejp_711_;
}
v_reusejp_711_:
{
return v___x_712_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___lam__1___boxed(lean_object* v_safety_718_, lean_object* v_env_719_, lean_object* v_vs_720_, lean_object* v___x_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
uint8_t v_safety_boxed_724_; lean_object* v_res_725_; 
v_safety_boxed_724_ = lean_unbox(v_safety_718_);
v_res_725_ = l_Lean4Lean_addMutual___lam__1(v_safety_boxed_724_, v_env_719_, v_vs_720_, v___x_721_, v___y_722_, v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v_vs_720_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___redArg(lean_object* v_as_x27_726_, lean_object* v_b_727_){
_start:
{
if (lean_obj_tag(v_as_x27_726_) == 0)
{
lean_object* v___x_728_; 
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_b_727_);
return v___x_728_;
}
else
{
lean_object* v_head_729_; lean_object* v_tail_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v_head_729_ = lean_ctor_get(v_as_x27_726_, 0);
v_tail_730_ = lean_ctor_get(v_as_x27_726_, 1);
lean_inc(v_head_729_);
v___x_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_731_, 0, v_head_729_);
v___x_732_ = lean_environment_add(v_b_727_, v___x_731_);
v_as_x27_726_ = v_tail_730_;
v_b_727_ = v___x_732_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___redArg___boxed(lean_object* v_as_x27_734_, lean_object* v_b_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___redArg(v_as_x27_734_, v_b_735_);
lean_dec(v_as_x27_734_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual(lean_object* v_env_747_, lean_object* v_vs_748_, uint8_t v_check_749_){
_start:
{
if (lean_obj_tag(v_vs_748_) == 1)
{
lean_object* v_head_750_; lean_object* v_toConstantVal_751_; uint8_t v_safety_752_; 
v_head_750_ = lean_ctor_get(v_vs_748_, 0);
v_toConstantVal_751_ = lean_ctor_get(v_head_750_, 0);
v_safety_752_ = lean_ctor_get_uint8(v_head_750_, sizeof(void*)*4);
if (v_safety_752_ == 1)
{
lean_object* v___x_769_; 
lean_dec_ref(v_vs_748_);
lean_dec_ref(v_env_747_);
v___x_769_ = ((lean_object*)(l_Lean4Lean_addMutual___closed__2));
return v___x_769_;
}
else
{
if (v_check_749_ == 0)
{
goto v___jp_753_;
}
else
{
lean_object* v_levelParams_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___f_774_; lean_object* v___x_775_; 
v_levelParams_770_ = lean_ctor_get(v_toConstantVal_751_, 1);
v___x_771_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
v___x_772_ = lean_box(0);
v___x_773_ = lean_box(v_safety_752_);
lean_inc_ref(v_vs_748_);
lean_inc_ref_n(v_env_747_, 2);
v___f_774_ = lean_alloc_closure((void*)(l_Lean4Lean_addMutual___lam__1___boxed), 6, 4);
lean_closure_set(v___f_774_, 0, v___x_773_);
lean_closure_set(v___f_774_, 1, v_env_747_);
lean_closure_set(v___f_774_, 2, v_vs_748_);
lean_closure_set(v___f_774_, 3, v___x_772_);
lean_inc(v_levelParams_770_);
v___x_775_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_env_747_, v_safety_752_, v___x_771_, v_levelParams_770_, v___f_774_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec_ref(v_vs_748_);
lean_dec_ref(v_env_747_);
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
else
{
lean_dec_ref(v___x_775_);
goto v___jp_753_;
}
}
}
v___jp_753_:
{
lean_object* v___x_754_; 
v___x_754_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___redArg(v_vs_748_, v_env_747_);
if (v_check_749_ == 0)
{
lean_dec_ref(v_vs_748_);
return v___x_754_;
}
else
{
lean_object* v_a_755_; lean_object* v_levelParams_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___f_759_; lean_object* v___x_760_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc_n(v_a_755_, 2);
v_levelParams_756_ = lean_ctor_get(v_toConstantVal_751_, 1);
lean_inc(v_levelParams_756_);
v___x_757_ = lean_obj_once(&l_Lean4Lean_addAxiom___closed__4, &l_Lean4Lean_addAxiom___closed__4_once, _init_l_Lean4Lean_addAxiom___closed__4);
v___x_758_ = lean_box(0);
v___f_759_ = lean_alloc_closure((void*)(l_Lean4Lean_addMutual___lam__0___boxed), 5, 3);
lean_closure_set(v___f_759_, 0, v_a_755_);
lean_closure_set(v___f_759_, 1, v_vs_748_);
lean_closure_set(v___f_759_, 2, v___x_758_);
v___x_760_ = l_Lean_Kernel_TypeChecker_M_run___redArg(v_a_755_, v_safety_752_, v___x_757_, v_levelParams_756_, v___f_759_);
if (lean_obj_tag(v___x_760_) == 0)
{
lean_object* v_a_761_; lean_object* v___x_763_; uint8_t v_isShared_764_; uint8_t v_isSharedCheck_768_; 
lean_dec_ref(v___x_754_);
v_a_761_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_768_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_768_ == 0)
{
v___x_763_ = v___x_760_;
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
else
{
lean_inc(v_a_761_);
lean_dec(v___x_760_);
v___x_763_ = lean_box(0);
v_isShared_764_ = v_isSharedCheck_768_;
goto v_resetjp_762_;
}
v_resetjp_762_:
{
lean_object* v___x_766_; 
if (v_isShared_764_ == 0)
{
v___x_766_ = v___x_763_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_a_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
else
{
lean_dec_ref(v___x_760_);
return v___x_754_;
}
}
}
}
else
{
lean_object* v___x_784_; 
lean_dec(v_vs_748_);
lean_dec_ref(v_env_747_);
v___x_784_ = ((lean_object*)(l_Lean4Lean_addMutual___closed__5));
return v___x_784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addMutual___boxed(lean_object* v_env_785_, lean_object* v_vs_786_, lean_object* v_check_787_){
_start:
{
uint8_t v_check_boxed_788_; lean_object* v_res_789_; 
v_check_boxed_788_ = lean_unbox(v_check_787_);
v_res_789_ = l_Lean4Lean_addMutual(v_env_785_, v_vs_786_, v_check_boxed_788_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0(lean_object* v_as_790_, lean_object* v_as_x27_791_, lean_object* v_b_792_, lean_object* v_a_793_){
_start:
{
lean_object* v___x_794_; 
v___x_794_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___redArg(v_as_x27_791_, v_b_792_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0___boxed(lean_object* v_as_795_, lean_object* v_as_x27_796_, lean_object* v_b_797_, lean_object* v_a_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__0(v_as_795_, v_as_x27_796_, v_b_797_, v_a_798_);
lean_dec(v_as_x27_796_);
lean_dec(v_as_795_);
return v_res_799_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1(lean_object* v_a_800_, lean_object* v_vs_801_, lean_object* v_as_802_, lean_object* v_as_x27_803_, lean_object* v_b_804_, lean_object* v_a_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_808_; 
v___x_808_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___redArg(v_a_800_, v_vs_801_, v_as_x27_803_, v_b_804_, v___y_806_, v___y_807_);
return v___x_808_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1___boxed(lean_object* v_a_809_, lean_object* v_vs_810_, lean_object* v_as_811_, lean_object* v_as_x27_812_, lean_object* v_b_813_, lean_object* v_a_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__1(v_a_809_, v_vs_810_, v_as_811_, v_as_x27_812_, v_b_813_, v_a_814_, v___y_815_, v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v_as_x27_812_);
lean_dec(v_as_811_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2(uint8_t v___x_818_, lean_object* v_env_819_, lean_object* v_as_820_, lean_object* v_as_x27_821_, lean_object* v_b_822_, lean_object* v_a_823_, lean_object* v___y_824_, lean_object* v___y_825_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___redArg(v___x_818_, v_env_819_, v_as_x27_821_, v_b_822_, v___y_824_, v___y_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2___boxed(lean_object* v___x_827_, lean_object* v_env_828_, lean_object* v_as_829_, lean_object* v_as_x27_830_, lean_object* v_b_831_, lean_object* v_a_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
uint8_t v___x_7715__boxed_835_; lean_object* v_res_836_; 
v___x_7715__boxed_835_ = lean_unbox(v___x_827_);
v_res_836_ = l_List_forIn_x27_loop___at___00Lean4Lean_addMutual_spec__2(v___x_7715__boxed_835_, v_env_828_, v_as_829_, v_as_x27_830_, v_b_831_, v_a_832_, v___y_833_, v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v_as_x27_830_);
lean_dec(v_as_829_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addDecl(lean_object* v_env_837_, lean_object* v_decl_838_, uint8_t v_check_839_){
_start:
{
switch(lean_obj_tag(v_decl_838_))
{
case 0:
{
lean_object* v_val_840_; lean_object* v___x_841_; 
v_val_840_ = lean_ctor_get(v_decl_838_, 0);
lean_inc_ref(v_val_840_);
lean_dec_ref(v_decl_838_);
v___x_841_ = l_Lean4Lean_addAxiom(v_env_837_, v_val_840_, v_check_839_);
return v___x_841_;
}
case 1:
{
lean_object* v_val_842_; lean_object* v___x_843_; 
v_val_842_ = lean_ctor_get(v_decl_838_, 0);
lean_inc_ref(v_val_842_);
lean_dec_ref(v_decl_838_);
v___x_843_ = l_Lean4Lean_addDefinition(v_env_837_, v_val_842_, v_check_839_);
return v___x_843_;
}
case 2:
{
lean_object* v_val_844_; lean_object* v___x_845_; 
v_val_844_ = lean_ctor_get(v_decl_838_, 0);
lean_inc_ref(v_val_844_);
lean_dec_ref(v_decl_838_);
v___x_845_ = l_Lean4Lean_addTheorem(v_env_837_, v_val_844_, v_check_839_);
return v___x_845_;
}
case 3:
{
lean_object* v_val_846_; lean_object* v___x_847_; 
v_val_846_ = lean_ctor_get(v_decl_838_, 0);
lean_inc_ref(v_val_846_);
lean_dec_ref(v_decl_838_);
v___x_847_ = l_Lean4Lean_addOpaque(v_env_837_, v_val_846_, v_check_839_);
return v___x_847_;
}
case 4:
{
lean_object* v___x_848_; 
v___x_848_ = l_Lean_Kernel_Environment_addQuot(v_env_837_);
return v___x_848_;
}
case 5:
{
lean_object* v_defns_849_; lean_object* v___x_850_; 
v_defns_849_ = lean_ctor_get(v_decl_838_, 0);
lean_inc(v_defns_849_);
lean_dec_ref(v_decl_838_);
v___x_850_ = l_Lean4Lean_addMutual(v_env_837_, v_defns_849_, v_check_839_);
return v___x_850_;
}
default: 
{
lean_object* v_lparams_851_; lean_object* v_nparams_852_; lean_object* v_types_853_; uint8_t v_isUnsafe_854_; lean_object* v___x_855_; 
v_lparams_851_ = lean_ctor_get(v_decl_838_, 0);
lean_inc(v_lparams_851_);
v_nparams_852_ = lean_ctor_get(v_decl_838_, 1);
lean_inc(v_nparams_852_);
v_types_853_ = lean_ctor_get(v_decl_838_, 2);
lean_inc(v_types_853_);
v_isUnsafe_854_ = lean_ctor_get_uint8(v_decl_838_, sizeof(void*)*3);
lean_dec_ref(v_decl_838_);
v___x_855_ = l_Lean4Lean_Environment_checkPrimitiveInductive(v_env_837_, v_lparams_851_, v_nparams_852_, v_types_853_, v_isUnsafe_854_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
lean_dec(v_types_853_);
lean_dec(v_nparams_852_);
lean_dec(v_lparams_851_);
lean_dec_ref(v_env_837_);
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_object* v_a_864_; uint8_t v___x_865_; lean_object* v___x_866_; 
v_a_864_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_864_);
lean_dec_ref(v___x_855_);
v___x_865_ = lean_unbox(v_a_864_);
lean_dec(v_a_864_);
v___x_866_ = l_Lean4Lean_Environment_addInductive(v_env_837_, v_lparams_851_, v_nparams_852_, v_types_853_, v_isUnsafe_854_, v___x_865_);
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_addDecl___boxed(lean_object* v_env_867_, lean_object* v_decl_868_, lean_object* v_check_869_){
_start:
{
uint8_t v_check_boxed_870_; lean_object* v_res_871_; 
v_check_boxed_870_ = lean_unbox(v_check_869_);
v_res_871_ = l_Lean4Lean_addDecl(v_env_867_, v_decl_868_, v_check_boxed_870_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_addDecl(lean_object* v_env_872_, lean_object* v_decl_873_, uint8_t v_check_874_){
_start:
{
lean_object* v___x_875_; 
v___x_875_ = l_Lean4Lean_addDecl(v_env_872_, v_decl_873_, v_check_874_);
return v___x_875_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_addDecl___boxed(lean_object* v_env_876_, lean_object* v_decl_877_, lean_object* v_check_878_){
_start:
{
uint8_t v_check_boxed_879_; lean_object* v_res_880_; 
v_check_boxed_879_ = lean_unbox(v_check_878_);
v_res_880_ = l_Lean_Kernel_addDecl(v_env_876_, v_decl_877_, v_check_boxed_879_);
return v_res_880_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_addDeclImpl___redArg(lean_object* v_env_881_, lean_object* v_decl_882_){
_start:
{
uint8_t v___x_883_; lean_object* v___x_884_; 
v___x_883_ = 1;
v___x_884_ = l_Lean4Lean_addDecl(v_env_881_, v_decl_882_, v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* lean_kernel_add_decl_impl(lean_object* v_env_885_, size_t v___maxHeartbeats_886_, lean_object* v_decl_887_, lean_object* v___cancelTk_x3f_888_){
_start:
{
lean_object* v___x_889_; 
lean_dec(v___cancelTk_x3f_888_);
v___x_889_ = l_Lean_Kernel_addDeclImpl___redArg(v_env_885_, v_decl_887_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_addDeclImpl___boxed(lean_object* v_env_890_, lean_object* v___maxHeartbeats_891_, lean_object* v_decl_892_, lean_object* v___cancelTk_x3f_893_){
_start:
{
size_t v___maxHeartbeats_boxed_894_; lean_object* v_res_895_; 
v___maxHeartbeats_boxed_894_ = lean_unbox_usize(v___maxHeartbeats_891_);
lean_dec(v___maxHeartbeats_891_);
v_res_895_ = lean_kernel_add_decl_impl(v_env_890_, v___maxHeartbeats_boxed_894_, v_decl_892_, v___cancelTk_x3f_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* lean_kernel_add_decl_without_checking_impl(lean_object* v_env_896_, lean_object* v_decl_897_){
_start:
{
uint8_t v___x_898_; lean_object* v___x_899_; 
v___x_898_ = 0;
v___x_899_ = l_Lean4Lean_addDecl(v_env_896_, v_decl_897_, v___x_898_);
return v___x_899_;
}
}
lean_object* runtime_initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Quot(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Inductive_Add(uint8_t builtin);
lean_object* runtime_initialize_Lean_Kernel_Primitive(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Environment(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Quot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Inductive_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Primitive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Environment(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Quot(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Inductive_Add(uint8_t builtin);
lean_object* initialize_Lean_Kernel_Primitive(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Environment(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Quot(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Inductive_Add(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Kernel_Primitive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Environment(builtin);
}
#ifdef __cplusplus
}
#endif
