// Lean compiler output
// Module: Lean.Kernel.ForEachExprV
// Imports: public import Lean.Expr public import Lean.Util.MonadCache
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
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_hash___boxed(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__7(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_ForEachExprV_visit___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_eqv___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExprV_visit___redArg___closed__0 = (const lean_object*)&l_Lean_ForEachExprV_visit___redArg___closed__0_value;
static const lean_closure_object l_Lean_ForEachExprV_visit___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_ForEachExprV_visit___redArg___closed__1 = (const lean_object*)&l_Lean_ForEachExprV_visit___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27___redArg___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Expr_forEachV_x27___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_forEachV_x27___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Expr_forEachV_x27___redArg___closed__0 = (const lean_object*)&l_Lean_Expr_forEachV_x27___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Expr_forEachV_x27___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEachV_x27___redArg___closed__1;
static lean_once_cell_t l_Lean_Expr_forEachV_x27___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_forEachV_x27___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__9(lean_object* v___x_1_, lean_object* v___x_2_, lean_object* v_e_3_, lean_object* v_toPure_4_, lean_object* v_____x_5_){
_start:
{
lean_object* v_fst_6_; lean_object* v_snd_7_; lean_object* v___x_9_; uint8_t v_isShared_10_; uint8_t v_isSharedCheck_16_; 
v_fst_6_ = lean_ctor_get(v_____x_5_, 0);
v_snd_7_ = lean_ctor_get(v_____x_5_, 1);
v_isSharedCheck_16_ = !lean_is_exclusive(v_____x_5_);
if (v_isSharedCheck_16_ == 0)
{
v___x_9_ = v_____x_5_;
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
else
{
lean_inc(v_snd_7_);
lean_inc(v_fst_6_);
lean_dec(v_____x_5_);
v___x_9_ = lean_box(0);
v_isShared_10_ = v_isSharedCheck_16_;
goto v_resetjp_8_;
}
v_resetjp_8_:
{
lean_object* v___x_11_; lean_object* v___x_13_; 
v___x_11_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___redArg(v___x_1_, v___x_2_, v_fst_6_, v_e_3_);
lean_dec(v_fst_6_);
if (v_isShared_10_ == 0)
{
lean_ctor_set(v___x_9_, 0, v___x_11_);
v___x_13_ = v___x_9_;
goto v_reusejp_12_;
}
else
{
lean_object* v_reuseFailAlloc_15_; 
v_reuseFailAlloc_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_15_, 0, v___x_11_);
lean_ctor_set(v_reuseFailAlloc_15_, 1, v_snd_7_);
v___x_13_ = v_reuseFailAlloc_15_;
goto v_reusejp_12_;
}
v_reusejp_12_:
{
lean_object* v___x_14_; 
v___x_14_ = lean_apply_2(v_toPure_4_, lean_box(0), v___x_13_);
return v___x_14_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__5(lean_object* v_fst_17_, lean_object* v_toPure_18_, lean_object* v_____x_19_){
_start:
{
lean_object* v_snd_20_; lean_object* v___x_22_; uint8_t v_isShared_23_; uint8_t v_isSharedCheck_28_; 
v_snd_20_ = lean_ctor_get(v_____x_19_, 1);
v_isSharedCheck_28_ = !lean_is_exclusive(v_____x_19_);
if (v_isSharedCheck_28_ == 0)
{
lean_object* v_unused_29_; 
v_unused_29_ = lean_ctor_get(v_____x_19_, 0);
lean_dec(v_unused_29_);
v___x_22_ = v_____x_19_;
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
else
{
lean_inc(v_snd_20_);
lean_dec(v_____x_19_);
v___x_22_ = lean_box(0);
v_isShared_23_ = v_isSharedCheck_28_;
goto v_resetjp_21_;
}
v_resetjp_21_:
{
lean_object* v___x_25_; 
if (v_isShared_23_ == 0)
{
lean_ctor_set(v___x_22_, 0, v_fst_17_);
v___x_25_ = v___x_22_;
goto v_reusejp_24_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_fst_17_);
lean_ctor_set(v_reuseFailAlloc_27_, 1, v_snd_20_);
v___x_25_ = v_reuseFailAlloc_27_;
goto v_reusejp_24_;
}
v_reusejp_24_:
{
lean_object* v___x_26_; 
v___x_26_ = lean_apply_2(v_toPure_18_, lean_box(0), v___x_25_);
return v___x_26_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__6(lean_object* v_toPure_30_, lean_object* v___x_31_, lean_object* v___x_32_, lean_object* v_e_33_, lean_object* v_toBind_34_, lean_object* v_____x_35_){
_start:
{
lean_object* v_fst_36_; lean_object* v_snd_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_49_; 
v_fst_36_ = lean_ctor_get(v_____x_35_, 0);
v_snd_37_ = lean_ctor_get(v_____x_35_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_____x_35_);
if (v_isSharedCheck_49_ == 0)
{
v___x_39_ = v_____x_35_;
v_isShared_40_ = v_isSharedCheck_49_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_snd_37_);
lean_inc(v_fst_36_);
lean_dec(v_____x_35_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_49_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___f_41_; lean_object* v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
lean_inc(v_toPure_30_);
lean_inc(v_fst_36_);
v___f_41_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__5), 3, 2);
lean_closure_set(v___f_41_, 0, v_fst_36_);
lean_closure_set(v___f_41_, 1, v_toPure_30_);
v___x_42_ = lean_box(0);
v___x_43_ = l_Std_DHashMap_Internal_Raw_u2080_insert___redArg(v___x_31_, v___x_32_, v_snd_37_, v_e_33_, v_fst_36_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 1, v___x_43_);
lean_ctor_set(v___x_39_, 0, v___x_42_);
v___x_45_ = v___x_39_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_43_);
v___x_45_ = v_reuseFailAlloc_48_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_apply_2(v_toPure_30_, lean_box(0), v___x_45_);
v___x_47_ = lean_apply_4(v_toBind_34_, lean_box(0), lean_box(0), v___x_46_, v___f_41_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__7(lean_object* v_snd_50_, lean_object* v_toPure_51_, uint8_t v_a_52_){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_53_ = lean_box(v_a_52_);
v___x_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_54_, 0, v___x_53_);
lean_ctor_set(v___x_54_, 1, v_snd_50_);
v___x_55_ = lean_apply_2(v_toPure_51_, lean_box(0), v___x_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__7___boxed(lean_object* v_snd_56_, lean_object* v_toPure_57_, lean_object* v_a_58_){
_start:
{
uint8_t v_a_boxed_59_; lean_object* v_res_60_; 
v_a_boxed_59_ = lean_unbox(v_a_58_);
v_res_60_ = l_Lean_ForEachExprV_visit___redArg___lam__7(v_snd_56_, v_toPure_57_, v_a_boxed_59_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__8(lean_object* v_g_61_, lean_object* v_e_62_, lean_object* v_toPure_63_, lean_object* v_toBind_64_, lean_object* v___f_65_, lean_object* v___f_66_, lean_object* v_____x_67_){
_start:
{
lean_object* v_fst_68_; 
v_fst_68_ = lean_ctor_get(v_____x_67_, 0);
if (lean_obj_tag(v_fst_68_) == 0)
{
lean_object* v_snd_69_; lean_object* v___x_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_snd_69_ = lean_ctor_get(v_____x_67_, 1);
lean_inc(v_snd_69_);
lean_dec_ref(v_____x_67_);
v___x_70_ = lean_apply_1(v_g_61_, v_e_62_);
v___f_71_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__7___boxed), 3, 2);
lean_closure_set(v___f_71_, 0, v_snd_69_);
lean_closure_set(v___f_71_, 1, v_toPure_63_);
lean_inc_n(v_toBind_64_, 2);
v___x_72_ = lean_apply_4(v_toBind_64_, lean_box(0), lean_box(0), v___x_70_, v___f_71_);
v___x_73_ = lean_apply_4(v_toBind_64_, lean_box(0), lean_box(0), v___x_72_, v___f_65_);
v___x_74_ = lean_apply_4(v_toBind_64_, lean_box(0), lean_box(0), v___x_73_, v___f_66_);
return v___x_74_;
}
else
{
lean_object* v_snd_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_84_; 
lean_inc_ref(v_fst_68_);
lean_dec(v___f_66_);
lean_dec(v___f_65_);
lean_dec(v_toBind_64_);
lean_dec_ref(v_e_62_);
lean_dec(v_g_61_);
v_snd_75_ = lean_ctor_get(v_____x_67_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v_____x_67_);
if (v_isSharedCheck_84_ == 0)
{
lean_object* v_unused_85_; 
v_unused_85_ = lean_ctor_get(v_____x_67_, 0);
lean_dec(v_unused_85_);
v___x_77_ = v_____x_67_;
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_snd_75_);
lean_dec(v_____x_67_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_84_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v_val_79_; lean_object* v___x_81_; 
v_val_79_ = lean_ctor_get(v_fst_68_, 0);
lean_inc(v_val_79_);
lean_dec_ref(v_fst_68_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v_val_79_);
v___x_81_ = v___x_77_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_val_79_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_snd_75_);
v___x_81_ = v_reuseFailAlloc_83_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
lean_object* v___x_82_; 
v___x_82_ = lean_apply_2(v_toPure_63_, lean_box(0), v___x_81_);
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__1(lean_object* v_inst_86_, lean_object* v_g_87_, lean_object* v_body_88_, lean_object* v_____x_89_){
_start:
{
lean_object* v_snd_90_; lean_object* v___x_91_; 
v_snd_90_ = lean_ctor_get(v_____x_89_, 1);
lean_inc(v_snd_90_);
lean_dec_ref(v_____x_89_);
v___x_91_ = l_Lean_ForEachExprV_visit___redArg(v_inst_86_, v_g_87_, v_body_88_, v_snd_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__2(lean_object* v_inst_92_, lean_object* v_g_93_, lean_object* v_value_94_, lean_object* v_toBind_95_, lean_object* v___f_96_, lean_object* v_____x_97_){
_start:
{
lean_object* v_snd_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_snd_98_ = lean_ctor_get(v_____x_97_, 1);
lean_inc(v_snd_98_);
lean_dec_ref(v_____x_97_);
v___x_99_ = l_Lean_ForEachExprV_visit___redArg(v_inst_92_, v_g_93_, v_value_94_, v_snd_98_);
v___x_100_ = lean_apply_4(v_toBind_95_, lean_box(0), lean_box(0), v___x_99_, v___f_96_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__3(lean_object* v_inst_101_, lean_object* v_g_102_, lean_object* v_arg_103_, lean_object* v_____x_104_){
_start:
{
lean_object* v_snd_105_; lean_object* v___x_106_; 
v_snd_105_ = lean_ctor_get(v_____x_104_, 1);
lean_inc(v_snd_105_);
lean_dec_ref(v_____x_104_);
v___x_106_ = l_Lean_ForEachExprV_visit___redArg(v_inst_101_, v_g_102_, v_arg_103_, v_snd_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__4(lean_object* v_toPure_107_, lean_object* v_inst_108_, lean_object* v_g_109_, lean_object* v_toBind_110_, lean_object* v_e_111_, lean_object* v_____x_112_){
_start:
{
lean_object* v_d_114_; lean_object* v_b_115_; lean_object* v___y_116_; lean_object* v_fst_120_; uint8_t v___x_121_; 
v_fst_120_ = lean_ctor_get(v_____x_112_, 0);
v___x_121_ = lean_unbox(v_fst_120_);
if (v___x_121_ == 0)
{
lean_object* v_snd_122_; lean_object* v___x_124_; uint8_t v_isShared_125_; uint8_t v_isSharedCheck_131_; 
lean_dec_ref(v_e_111_);
lean_dec(v_toBind_110_);
lean_dec(v_g_109_);
lean_dec_ref(v_inst_108_);
v_snd_122_ = lean_ctor_get(v_____x_112_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_____x_112_);
if (v_isSharedCheck_131_ == 0)
{
lean_object* v_unused_132_; 
v_unused_132_ = lean_ctor_get(v_____x_112_, 0);
lean_dec(v_unused_132_);
v___x_124_ = v_____x_112_;
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
else
{
lean_inc(v_snd_122_);
lean_dec(v_____x_112_);
v___x_124_ = lean_box(0);
v_isShared_125_ = v_isSharedCheck_131_;
goto v_resetjp_123_;
}
v_resetjp_123_:
{
lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_126_ = lean_box(0);
if (v_isShared_125_ == 0)
{
lean_ctor_set(v___x_124_, 0, v___x_126_);
v___x_128_ = v___x_124_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_snd_122_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
lean_object* v___x_129_; 
v___x_129_ = lean_apply_2(v_toPure_107_, lean_box(0), v___x_128_);
return v___x_129_;
}
}
}
else
{
switch(lean_obj_tag(v_e_111_))
{
case 7:
{
lean_object* v_snd_133_; lean_object* v_binderType_134_; lean_object* v_body_135_; 
lean_dec(v_toPure_107_);
v_snd_133_ = lean_ctor_get(v_____x_112_, 1);
lean_inc(v_snd_133_);
lean_dec_ref(v_____x_112_);
v_binderType_134_ = lean_ctor_get(v_e_111_, 1);
lean_inc_ref(v_binderType_134_);
v_body_135_ = lean_ctor_get(v_e_111_, 2);
lean_inc_ref(v_body_135_);
lean_dec_ref(v_e_111_);
v_d_114_ = v_binderType_134_;
v_b_115_ = v_body_135_;
v___y_116_ = v_snd_133_;
goto v___jp_113_;
}
case 6:
{
lean_object* v_snd_136_; lean_object* v_binderType_137_; lean_object* v_body_138_; 
lean_dec(v_toPure_107_);
v_snd_136_ = lean_ctor_get(v_____x_112_, 1);
lean_inc(v_snd_136_);
lean_dec_ref(v_____x_112_);
v_binderType_137_ = lean_ctor_get(v_e_111_, 1);
lean_inc_ref(v_binderType_137_);
v_body_138_ = lean_ctor_get(v_e_111_, 2);
lean_inc_ref(v_body_138_);
lean_dec_ref(v_e_111_);
v_d_114_ = v_binderType_137_;
v_b_115_ = v_body_138_;
v___y_116_ = v_snd_136_;
goto v___jp_113_;
}
case 8:
{
lean_object* v_snd_139_; lean_object* v_type_140_; lean_object* v_value_141_; lean_object* v_body_142_; lean_object* v___f_143_; lean_object* v___f_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
lean_dec(v_toPure_107_);
v_snd_139_ = lean_ctor_get(v_____x_112_, 1);
lean_inc(v_snd_139_);
lean_dec_ref(v_____x_112_);
v_type_140_ = lean_ctor_get(v_e_111_, 1);
lean_inc_ref(v_type_140_);
v_value_141_ = lean_ctor_get(v_e_111_, 2);
lean_inc_ref(v_value_141_);
v_body_142_ = lean_ctor_get(v_e_111_, 3);
lean_inc_ref(v_body_142_);
lean_dec_ref(v_e_111_);
lean_inc_n(v_g_109_, 2);
lean_inc_ref_n(v_inst_108_, 2);
v___f_143_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__1), 4, 3);
lean_closure_set(v___f_143_, 0, v_inst_108_);
lean_closure_set(v___f_143_, 1, v_g_109_);
lean_closure_set(v___f_143_, 2, v_body_142_);
lean_inc(v_toBind_110_);
v___f_144_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__2), 6, 5);
lean_closure_set(v___f_144_, 0, v_inst_108_);
lean_closure_set(v___f_144_, 1, v_g_109_);
lean_closure_set(v___f_144_, 2, v_value_141_);
lean_closure_set(v___f_144_, 3, v_toBind_110_);
lean_closure_set(v___f_144_, 4, v___f_143_);
v___x_145_ = l_Lean_ForEachExprV_visit___redArg(v_inst_108_, v_g_109_, v_type_140_, v_snd_139_);
v___x_146_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_145_, v___f_144_);
return v___x_146_;
}
case 5:
{
lean_object* v_snd_147_; lean_object* v_fn_148_; lean_object* v_arg_149_; lean_object* v___f_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
lean_dec(v_toPure_107_);
v_snd_147_ = lean_ctor_get(v_____x_112_, 1);
lean_inc(v_snd_147_);
lean_dec_ref(v_____x_112_);
v_fn_148_ = lean_ctor_get(v_e_111_, 0);
lean_inc_ref(v_fn_148_);
v_arg_149_ = lean_ctor_get(v_e_111_, 1);
lean_inc_ref(v_arg_149_);
lean_dec_ref(v_e_111_);
lean_inc(v_g_109_);
lean_inc_ref(v_inst_108_);
v___f_150_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__3), 4, 3);
lean_closure_set(v___f_150_, 0, v_inst_108_);
lean_closure_set(v___f_150_, 1, v_g_109_);
lean_closure_set(v___f_150_, 2, v_arg_149_);
v___x_151_ = l_Lean_ForEachExprV_visit___redArg(v_inst_108_, v_g_109_, v_fn_148_, v_snd_147_);
v___x_152_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_151_, v___f_150_);
return v___x_152_;
}
case 10:
{
lean_object* v_snd_153_; lean_object* v_expr_154_; lean_object* v___x_155_; 
lean_dec(v_toBind_110_);
lean_dec(v_toPure_107_);
v_snd_153_ = lean_ctor_get(v_____x_112_, 1);
lean_inc(v_snd_153_);
lean_dec_ref(v_____x_112_);
v_expr_154_ = lean_ctor_get(v_e_111_, 1);
lean_inc_ref(v_expr_154_);
lean_dec_ref(v_e_111_);
v___x_155_ = l_Lean_ForEachExprV_visit___redArg(v_inst_108_, v_g_109_, v_expr_154_, v_snd_153_);
return v___x_155_;
}
case 11:
{
lean_object* v_snd_156_; lean_object* v_struct_157_; lean_object* v___x_158_; 
lean_dec(v_toBind_110_);
lean_dec(v_toPure_107_);
v_snd_156_ = lean_ctor_get(v_____x_112_, 1);
lean_inc(v_snd_156_);
lean_dec_ref(v_____x_112_);
v_struct_157_ = lean_ctor_get(v_e_111_, 2);
lean_inc_ref(v_struct_157_);
lean_dec_ref(v_e_111_);
v___x_158_ = l_Lean_ForEachExprV_visit___redArg(v_inst_108_, v_g_109_, v_struct_157_, v_snd_156_);
return v___x_158_;
}
default: 
{
lean_object* v_snd_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_168_; 
lean_dec_ref(v_e_111_);
lean_dec(v_toBind_110_);
lean_dec(v_g_109_);
lean_dec_ref(v_inst_108_);
v_snd_159_ = lean_ctor_get(v_____x_112_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_____x_112_);
if (v_isSharedCheck_168_ == 0)
{
lean_object* v_unused_169_; 
v_unused_169_ = lean_ctor_get(v_____x_112_, 0);
lean_dec(v_unused_169_);
v___x_161_ = v_____x_112_;
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_snd_159_);
lean_dec(v_____x_112_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_163_ = lean_box(0);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_165_ = v___x_161_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v_snd_159_);
v___x_165_ = v_reuseFailAlloc_167_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
lean_object* v___x_166_; 
v___x_166_ = lean_apply_2(v_toPure_107_, lean_box(0), v___x_165_);
return v___x_166_;
}
}
}
}
}
v___jp_113_:
{
lean_object* v___f_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
lean_inc(v_g_109_);
lean_inc_ref(v_inst_108_);
v___f_117_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__0), 4, 3);
lean_closure_set(v___f_117_, 0, v_inst_108_);
lean_closure_set(v___f_117_, 1, v_g_109_);
lean_closure_set(v___f_117_, 2, v_b_115_);
v___x_118_ = l_Lean_ForEachExprV_visit___redArg(v_inst_108_, v_g_109_, v_d_114_, v___y_116_);
v___x_119_ = lean_apply_4(v_toBind_110_, lean_box(0), lean_box(0), v___x_118_, v___f_117_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg(lean_object* v_inst_172_, lean_object* v_g_173_, lean_object* v_e_174_, lean_object* v_a_175_){
_start:
{
lean_object* v_toApplicative_176_; lean_object* v_toBind_177_; lean_object* v_toPure_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; lean_object* v___f_182_; lean_object* v___f_183_; lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_toApplicative_176_ = lean_ctor_get(v_inst_172_, 0);
v_toBind_177_ = lean_ctor_get(v_inst_172_, 1);
lean_inc_n(v_toBind_177_, 5);
v_toPure_178_ = lean_ctor_get(v_toApplicative_176_, 1);
lean_inc_n(v_toPure_178_, 5);
lean_inc_ref_n(v_e_174_, 3);
lean_inc(v_g_173_);
v___f_179_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__4), 6, 5);
lean_closure_set(v___f_179_, 0, v_toPure_178_);
lean_closure_set(v___f_179_, 1, v_inst_172_);
lean_closure_set(v___f_179_, 2, v_g_173_);
lean_closure_set(v___f_179_, 3, v_toBind_177_);
lean_closure_set(v___f_179_, 4, v_e_174_);
v___x_180_ = ((lean_object*)(l_Lean_ForEachExprV_visit___redArg___closed__0));
v___x_181_ = ((lean_object*)(l_Lean_ForEachExprV_visit___redArg___closed__1));
v___f_182_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__6), 6, 5);
lean_closure_set(v___f_182_, 0, v_toPure_178_);
lean_closure_set(v___f_182_, 1, v___x_180_);
lean_closure_set(v___f_182_, 2, v___x_181_);
lean_closure_set(v___f_182_, 3, v_e_174_);
lean_closure_set(v___f_182_, 4, v_toBind_177_);
v___f_183_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__8), 7, 6);
lean_closure_set(v___f_183_, 0, v_g_173_);
lean_closure_set(v___f_183_, 1, v_e_174_);
lean_closure_set(v___f_183_, 2, v_toPure_178_);
lean_closure_set(v___f_183_, 3, v_toBind_177_);
lean_closure_set(v___f_183_, 4, v___f_179_);
lean_closure_set(v___f_183_, 5, v___f_182_);
v___f_184_ = lean_alloc_closure((void*)(l_Lean_ForEachExprV_visit___redArg___lam__9), 5, 4);
lean_closure_set(v___f_184_, 0, v___x_180_);
lean_closure_set(v___f_184_, 1, v___x_181_);
lean_closure_set(v___f_184_, 2, v_e_174_);
lean_closure_set(v___f_184_, 3, v_toPure_178_);
lean_inc_ref(v_a_175_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_a_175_);
lean_ctor_set(v___x_185_, 1, v_a_175_);
v___x_186_ = lean_apply_2(v_toPure_178_, lean_box(0), v___x_185_);
v___x_187_ = lean_apply_4(v_toBind_177_, lean_box(0), lean_box(0), v___x_186_, v___f_184_);
v___x_188_ = lean_apply_4(v_toBind_177_, lean_box(0), lean_box(0), v___x_187_, v___f_183_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit___redArg___lam__0(lean_object* v_inst_189_, lean_object* v_g_190_, lean_object* v_b_191_, lean_object* v_____x_192_){
_start:
{
lean_object* v_snd_193_; lean_object* v___x_194_; 
v_snd_193_ = lean_ctor_get(v_____x_192_, 1);
lean_inc(v_snd_193_);
lean_dec_ref(v_____x_192_);
v___x_194_ = l_Lean_ForEachExprV_visit___redArg(v_inst_189_, v_g_190_, v_b_191_, v_snd_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprV_visit(lean_object* v_m_195_, lean_object* v_inst_196_, lean_object* v_g_197_, lean_object* v_e_198_, lean_object* v_a_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Lean_ForEachExprV_visit___redArg(v_inst_196_, v_g_197_, v_e_198_, v_a_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27___redArg___lam__0(lean_object* v_x_201_){
_start:
{
lean_object* v_fst_202_; 
v_fst_202_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_fst_202_);
return v_fst_202_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27___redArg___lam__0___boxed(lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_Expr_forEachV_x27___redArg___lam__0(v_x_203_);
lean_dec_ref(v_x_203_);
return v_res_204_;
}
}
static lean_object* _init_l_Lean_Expr_forEachV_x27___redArg___closed__1(void){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_206_ = lean_box(0);
v___x_207_ = lean_unsigned_to_nat(16u);
v___x_208_ = lean_mk_array(v___x_207_, v___x_206_);
return v___x_208_;
}
}
static lean_object* _init_l_Lean_Expr_forEachV_x27___redArg___closed__2(void){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = lean_obj_once(&l_Lean_Expr_forEachV_x27___redArg___closed__1, &l_Lean_Expr_forEachV_x27___redArg___closed__1_once, _init_l_Lean_Expr_forEachV_x27___redArg___closed__1);
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_209_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27___redArg(lean_object* v_inst_212_, lean_object* v_e_213_, lean_object* v_f_214_){
_start:
{
lean_object* v_toApplicative_215_; lean_object* v_toFunctor_216_; lean_object* v_map_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_toApplicative_215_ = lean_ctor_get(v_inst_212_, 0);
v_toFunctor_216_ = lean_ctor_get(v_toApplicative_215_, 0);
v_map_217_ = lean_ctor_get(v_toFunctor_216_, 0);
lean_inc(v_map_217_);
v___f_218_ = ((lean_object*)(l_Lean_Expr_forEachV_x27___redArg___closed__0));
v___x_219_ = lean_obj_once(&l_Lean_Expr_forEachV_x27___redArg___closed__2, &l_Lean_Expr_forEachV_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEachV_x27___redArg___closed__2);
v___x_220_ = l_Lean_ForEachExprV_visit___redArg(v_inst_212_, v_f_214_, v_e_213_, v___x_219_);
v___x_221_ = lean_apply_4(v_map_217_, lean_box(0), lean_box(0), v___f_218_, v___x_220_);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV_x27(lean_object* v_m_222_, lean_object* v_inst_223_, lean_object* v_e_224_, lean_object* v_f_225_){
_start:
{
lean_object* v_toApplicative_226_; lean_object* v_toFunctor_227_; lean_object* v_map_228_; lean_object* v___f_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_toApplicative_226_ = lean_ctor_get(v_inst_223_, 0);
v_toFunctor_227_ = lean_ctor_get(v_toApplicative_226_, 0);
v_map_228_ = lean_ctor_get(v_toFunctor_227_, 0);
lean_inc(v_map_228_);
v___f_229_ = ((lean_object*)(l_Lean_Expr_forEachV_x27___redArg___closed__0));
v___x_230_ = lean_obj_once(&l_Lean_Expr_forEachV_x27___redArg___closed__2, &l_Lean_Expr_forEachV_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEachV_x27___redArg___closed__2);
v___x_231_ = l_Lean_ForEachExprV_visit___redArg(v_inst_223_, v_f_225_, v_e_224_, v___x_230_);
v___x_232_ = lean_apply_4(v_map_228_, lean_box(0), lean_box(0), v___f_229_, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV___redArg___lam__1(lean_object* v_toPure_233_, lean_object* v_____r_234_){
_start:
{
uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v___x_235_ = 1;
v___x_236_ = lean_box(v___x_235_);
v___x_237_ = lean_apply_2(v_toPure_233_, lean_box(0), v___x_236_);
return v___x_237_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV___redArg___lam__0(lean_object* v_f_238_, lean_object* v_toBind_239_, lean_object* v___f_240_, lean_object* v_e_241_){
_start:
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_apply_1(v_f_238_, v_e_241_);
v___x_243_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v___x_242_, v___f_240_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV___redArg(lean_object* v_inst_244_, lean_object* v_e_245_, lean_object* v_f_246_){
_start:
{
lean_object* v_toApplicative_247_; lean_object* v_toFunctor_248_; lean_object* v_toBind_249_; lean_object* v_toPure_250_; lean_object* v_map_251_; lean_object* v___f_252_; lean_object* v___f_253_; lean_object* v___f_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; 
v_toApplicative_247_ = lean_ctor_get(v_inst_244_, 0);
v_toFunctor_248_ = lean_ctor_get(v_toApplicative_247_, 0);
v_toBind_249_ = lean_ctor_get(v_inst_244_, 1);
v_toPure_250_ = lean_ctor_get(v_toApplicative_247_, 1);
v_map_251_ = lean_ctor_get(v_toFunctor_248_, 0);
lean_inc(v_map_251_);
v___f_252_ = ((lean_object*)(l_Lean_Expr_forEachV_x27___redArg___closed__0));
lean_inc(v_toPure_250_);
v___f_253_ = lean_alloc_closure((void*)(l_Lean_Expr_forEachV___redArg___lam__1), 2, 1);
lean_closure_set(v___f_253_, 0, v_toPure_250_);
lean_inc(v_toBind_249_);
v___f_254_ = lean_alloc_closure((void*)(l_Lean_Expr_forEachV___redArg___lam__0), 4, 3);
lean_closure_set(v___f_254_, 0, v_f_246_);
lean_closure_set(v___f_254_, 1, v_toBind_249_);
lean_closure_set(v___f_254_, 2, v___f_253_);
v___x_255_ = lean_obj_once(&l_Lean_Expr_forEachV_x27___redArg___closed__2, &l_Lean_Expr_forEachV_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEachV_x27___redArg___closed__2);
v___x_256_ = l_Lean_ForEachExprV_visit___redArg(v_inst_244_, v___f_254_, v_e_245_, v___x_255_);
v___x_257_ = lean_apply_4(v_map_251_, lean_box(0), lean_box(0), v___f_252_, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_forEachV(lean_object* v_m_258_, lean_object* v_inst_259_, lean_object* v_e_260_, lean_object* v_f_261_){
_start:
{
lean_object* v_toApplicative_262_; lean_object* v_toFunctor_263_; lean_object* v_toBind_264_; lean_object* v_toPure_265_; lean_object* v_map_266_; lean_object* v___f_267_; lean_object* v___f_268_; lean_object* v___f_269_; lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
v_toApplicative_262_ = lean_ctor_get(v_inst_259_, 0);
v_toFunctor_263_ = lean_ctor_get(v_toApplicative_262_, 0);
v_toBind_264_ = lean_ctor_get(v_inst_259_, 1);
v_toPure_265_ = lean_ctor_get(v_toApplicative_262_, 1);
v_map_266_ = lean_ctor_get(v_toFunctor_263_, 0);
lean_inc(v_map_266_);
v___f_267_ = ((lean_object*)(l_Lean_Expr_forEachV_x27___redArg___closed__0));
lean_inc(v_toPure_265_);
v___f_268_ = lean_alloc_closure((void*)(l_Lean_Expr_forEachV___redArg___lam__1), 2, 1);
lean_closure_set(v___f_268_, 0, v_toPure_265_);
lean_inc(v_toBind_264_);
v___f_269_ = lean_alloc_closure((void*)(l_Lean_Expr_forEachV___redArg___lam__0), 4, 3);
lean_closure_set(v___f_269_, 0, v_f_261_);
lean_closure_set(v___f_269_, 1, v_toBind_264_);
lean_closure_set(v___f_269_, 2, v___f_268_);
v___x_270_ = lean_obj_once(&l_Lean_Expr_forEachV_x27___redArg___closed__2, &l_Lean_Expr_forEachV_x27___redArg___closed__2_once, _init_l_Lean_Expr_forEachV_x27___redArg___closed__2);
v___x_271_ = l_Lean_ForEachExprV_visit___redArg(v_inst_259_, v___f_269_, v_e_260_, v___x_270_);
v___x_272_ = lean_apply_4(v_map_266_, lean_box(0), lean_box(0), v___f_267_, v___x_271_);
return v___x_272_;
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_MonadCache(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_ForEachExprV(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_ForEachExprV(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_Util_MonadCache(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_ForEachExprV(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_MonadCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_ForEachExprV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_ForEachExprV(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_ForEachExprV(builtin);
}
#ifdef __cplusplus
}
#endif
