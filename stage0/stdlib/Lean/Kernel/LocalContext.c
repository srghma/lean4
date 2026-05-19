// Lean compiler output
// Module: Lean.Kernel.LocalContext
// Imports: public import Lean.LocalContext
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
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg___lam__0(lean_object* v_f_1_, lean_object* v_c_2_, lean_object* v_x_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_apply_2(v_f_1_, v_x_3_, v_c_2_);
return v___x_4_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg___lam__1(lean_object* v_inst_5_, lean_object* v_00_u03b1_6_, lean_object* v_f_7_, lean_object* v_c_8_){
_start:
{
lean_object* v___f_9_; lean_object* v___x_10_; 
v___f_9_ = lean_alloc_closure((void*)(l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_9_, 0, v_f_7_);
lean_closure_set(v___f_9_, 1, v_c_8_);
v___x_10_ = lean_apply_2(v_inst_5_, lean_box(0), v___f_9_);
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg(lean_object* v_inst_11_){
_start:
{
lean_object* v___f_12_; 
v___f_12_ = lean_alloc_closure((void*)(l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_12_, 0, v_inst_11_);
return v___f_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_instMonadLocalNameGeneratorReaderT(lean_object* v_m_13_, lean_object* v_00_u03c1_14_, lean_object* v_inst_15_){
_start:
{
lean_object* v___f_16_; 
v___f_16_ = lean_alloc_closure((void*)(l_Lean_Kernel_instMonadLocalNameGeneratorReaderT___redArg___lam__1), 4, 1);
lean_closure_set(v___f_16_, 0, v_inst_15_);
return v___f_16_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__0(lean_object* v_id_17_, lean_object* v_name_18_, lean_object* v_ty_19_, uint8_t v_bi_20_, lean_object* v_x_21_){
_start:
{
uint8_t v___x_22_; lean_object* v___x_23_; 
v___x_22_ = 0;
v___x_23_ = l_Lean_LocalContext_mkLocalDecl(v_x_21_, v_id_17_, v_name_18_, v_ty_19_, v_bi_20_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__0___boxed(lean_object* v_id_24_, lean_object* v_name_25_, lean_object* v_ty_26_, lean_object* v_bi_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_bi_boxed_29_; lean_object* v_res_30_; 
v_bi_boxed_29_ = lean_unbox(v_bi_27_);
v_res_30_ = l_Lean_Kernel_withLocalDecl___redArg___lam__0(v_id_24_, v_name_25_, v_ty_26_, v_bi_boxed_29_, v_x_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__1(lean_object* v_name_31_, lean_object* v_ty_32_, uint8_t v_bi_33_, lean_object* v_k_34_, lean_object* v_inst_35_, lean_object* v_id_36_){
_start:
{
lean_object* v___x_37_; lean_object* v___f_38_; lean_object* v___x_39_; lean_object* v___x_40_; lean_object* v___x_41_; 
v___x_37_ = lean_box(v_bi_33_);
lean_inc(v_id_36_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_Kernel_withLocalDecl___redArg___lam__0___boxed), 5, 4);
lean_closure_set(v___f_38_, 0, v_id_36_);
lean_closure_set(v___f_38_, 1, v_name_31_);
lean_closure_set(v___f_38_, 2, v_ty_32_);
lean_closure_set(v___f_38_, 3, v___x_37_);
v___x_39_ = l_Lean_Expr_fvar___override(v_id_36_);
v___x_40_ = lean_apply_1(v_k_34_, v___x_39_);
v___x_41_ = lean_apply_3(v_inst_35_, lean_box(0), v___f_38_, v___x_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___lam__1___boxed(lean_object* v_name_42_, lean_object* v_ty_43_, lean_object* v_bi_44_, lean_object* v_k_45_, lean_object* v_inst_46_, lean_object* v_id_47_){
_start:
{
uint8_t v_bi_boxed_48_; lean_object* v_res_49_; 
v_bi_boxed_48_ = lean_unbox(v_bi_44_);
v_res_49_ = l_Lean_Kernel_withLocalDecl___redArg___lam__1(v_name_42_, v_ty_43_, v_bi_boxed_48_, v_k_45_, v_inst_46_, v_id_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg(lean_object* v_inst_50_, lean_object* v_inst_51_, lean_object* v_name_52_, uint8_t v_bi_53_, lean_object* v_ty_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___f_57_; lean_object* v___x_58_; 
v___x_56_ = lean_box(v_bi_53_);
v___f_57_ = lean_alloc_closure((void*)(l_Lean_Kernel_withLocalDecl___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_57_, 0, v_name_52_);
lean_closure_set(v___f_57_, 1, v_ty_54_);
lean_closure_set(v___f_57_, 2, v___x_56_);
lean_closure_set(v___f_57_, 3, v_k_55_);
lean_closure_set(v___f_57_, 4, v_inst_51_);
v___x_58_ = lean_apply_2(v_inst_50_, lean_box(0), v___f_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___redArg___boxed(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_name_61_, lean_object* v_bi_62_, lean_object* v_ty_63_, lean_object* v_k_64_){
_start:
{
uint8_t v_bi_boxed_65_; lean_object* v_res_66_; 
v_bi_boxed_65_ = lean_unbox(v_bi_62_);
v_res_66_ = l_Lean_Kernel_withLocalDecl___redArg(v_inst_59_, v_inst_60_, v_name_61_, v_bi_boxed_65_, v_ty_63_, v_k_64_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl(lean_object* v_m_67_, lean_object* v_00_u03b1_68_, lean_object* v_inst_69_, lean_object* v_inst_70_, lean_object* v_inst_71_, lean_object* v_name_72_, uint8_t v_bi_73_, lean_object* v_ty_74_, lean_object* v_k_75_){
_start:
{
lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v___x_78_; 
v___x_76_ = lean_box(v_bi_73_);
v___f_77_ = lean_alloc_closure((void*)(l_Lean_Kernel_withLocalDecl___redArg___lam__1___boxed), 6, 5);
lean_closure_set(v___f_77_, 0, v_name_72_);
lean_closure_set(v___f_77_, 1, v_ty_74_);
lean_closure_set(v___f_77_, 2, v___x_76_);
lean_closure_set(v___f_77_, 3, v_k_75_);
lean_closure_set(v___f_77_, 4, v_inst_71_);
v___x_78_ = lean_apply_2(v_inst_70_, lean_box(0), v___f_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLocalDecl___boxed(lean_object* v_m_79_, lean_object* v_00_u03b1_80_, lean_object* v_inst_81_, lean_object* v_inst_82_, lean_object* v_inst_83_, lean_object* v_name_84_, lean_object* v_bi_85_, lean_object* v_ty_86_, lean_object* v_k_87_){
_start:
{
uint8_t v_bi_boxed_88_; lean_object* v_res_89_; 
v_bi_boxed_88_ = lean_unbox(v_bi_85_);
v_res_89_ = l_Lean_Kernel_withLocalDecl(v_m_79_, v_00_u03b1_80_, v_inst_81_, v_inst_82_, v_inst_83_, v_name_84_, v_bi_boxed_88_, v_ty_86_, v_k_87_);
lean_dec_ref(v_inst_81_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___redArg___lam__0(lean_object* v_id_90_, lean_object* v_name_91_, lean_object* v_ty_92_, lean_object* v_val_93_, lean_object* v_x_94_){
_start:
{
uint8_t v___x_95_; uint8_t v___x_96_; lean_object* v___x_97_; 
v___x_95_ = 0;
v___x_96_ = 0;
v___x_97_ = l_Lean_LocalContext_mkLetDecl(v_x_94_, v_id_90_, v_name_91_, v_ty_92_, v_val_93_, v___x_95_, v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___redArg___lam__1(lean_object* v_name_98_, lean_object* v_ty_99_, lean_object* v_val_100_, lean_object* v_k_101_, lean_object* v_inst_102_, lean_object* v_id_103_){
_start:
{
lean_object* v___f_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
lean_inc(v_id_103_);
v___f_104_ = lean_alloc_closure((void*)(l_Lean_Kernel_withLetDecl___redArg___lam__0), 5, 4);
lean_closure_set(v___f_104_, 0, v_id_103_);
lean_closure_set(v___f_104_, 1, v_name_98_);
lean_closure_set(v___f_104_, 2, v_ty_99_);
lean_closure_set(v___f_104_, 3, v_val_100_);
v___x_105_ = l_Lean_Expr_fvar___override(v_id_103_);
v___x_106_ = lean_apply_1(v_k_101_, v___x_105_);
v___x_107_ = lean_apply_3(v_inst_102_, lean_box(0), v___f_104_, v___x_106_);
return v___x_107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___redArg(lean_object* v_inst_108_, lean_object* v_inst_109_, lean_object* v_name_110_, lean_object* v_ty_111_, lean_object* v_val_112_, lean_object* v_k_113_){
_start:
{
lean_object* v___f_114_; lean_object* v___x_115_; 
v___f_114_ = lean_alloc_closure((void*)(l_Lean_Kernel_withLetDecl___redArg___lam__1), 6, 5);
lean_closure_set(v___f_114_, 0, v_name_110_);
lean_closure_set(v___f_114_, 1, v_ty_111_);
lean_closure_set(v___f_114_, 2, v_val_112_);
lean_closure_set(v___f_114_, 3, v_k_113_);
lean_closure_set(v___f_114_, 4, v_inst_109_);
v___x_115_ = lean_apply_2(v_inst_108_, lean_box(0), v___f_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl(lean_object* v_m_116_, lean_object* v_00_u03b1_117_, lean_object* v_inst_118_, lean_object* v_inst_119_, lean_object* v_inst_120_, lean_object* v_name_121_, lean_object* v_ty_122_, lean_object* v_val_123_, lean_object* v_k_124_){
_start:
{
lean_object* v___f_125_; lean_object* v___x_126_; 
v___f_125_ = lean_alloc_closure((void*)(l_Lean_Kernel_withLetDecl___redArg___lam__1), 6, 5);
lean_closure_set(v___f_125_, 0, v_name_121_);
lean_closure_set(v___f_125_, 1, v_ty_122_);
lean_closure_set(v___f_125_, 2, v_val_123_);
lean_closure_set(v___f_125_, 3, v_k_124_);
lean_closure_set(v___f_125_, 4, v_inst_120_);
v___x_126_ = lean_apply_2(v_inst_119_, lean_box(0), v___f_125_);
return v___x_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_withLetDecl___boxed(lean_object* v_m_127_, lean_object* v_00_u03b1_128_, lean_object* v_inst_129_, lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_name_132_, lean_object* v_ty_133_, lean_object* v_val_134_, lean_object* v_k_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Kernel_withLetDecl(v_m_127_, v_00_u03b1_128_, v_inst_129_, v_inst_130_, v_inst_131_, v_name_132_, v_ty_133_, v_val_134_, v_k_135_);
lean_dec_ref(v_inst_129_);
return v_res_136_;
}
}
lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_LocalContext(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_LocalContext(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_LocalContext(builtin);
}
#ifdef __cplusplus
}
#endif
