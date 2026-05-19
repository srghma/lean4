// Lean compiler output
// Module: Lean.Kernel.Instantiate
// Imports: public import Lean.Expr public import Lean.LocalContext public import Lean.Util.InstantiateLevelParams
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_mkAppRange(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_cheapBetaReduce_cont_spec__0(lean_object*);
static const lean_string_object l_Lean_Expr_cheapBetaReduce_cont___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Lean.Kernel.Instantiate"};
static const lean_object* l_Lean_Expr_cheapBetaReduce_cont___closed__0 = (const lean_object*)&l_Lean_Expr_cheapBetaReduce_cont___closed__0_value;
static const lean_string_object l_Lean_Expr_cheapBetaReduce_cont___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Expr.cheapBetaReduce.cont"};
static const lean_object* l_Lean_Expr_cheapBetaReduce_cont___closed__1 = (const lean_object*)&l_Lean_Expr_cheapBetaReduce_cont___closed__1_value;
static const lean_string_object l_Lean_Expr_cheapBetaReduce_cont___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "assertion violation: n < i\n      "};
static const lean_object* l_Lean_Expr_cheapBetaReduce_cont___closed__2 = (const lean_object*)&l_Lean_Expr_cheapBetaReduce_cont___closed__2_value;
static lean_once_cell_t l_Lean_Expr_cheapBetaReduce_cont___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_cheapBetaReduce_cont___closed__3;
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_cont(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_cont___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_loop(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Expr_cheapBetaReduce___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_cheapBetaReduce___closed__0;
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Expr_cheapBetaReduce_cont_spec__0(lean_object* v_msg_1_){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = l_Lean_instInhabitedExpr;
v___x_3_ = lean_panic_fn_borrowed(v___x_2_, v_msg_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Expr_cheapBetaReduce_cont___closed__3(void){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_7_ = ((lean_object*)(l_Lean_Expr_cheapBetaReduce_cont___closed__2));
v___x_8_ = lean_unsigned_to_nat(6u);
v___x_9_ = lean_unsigned_to_nat(23u);
v___x_10_ = ((lean_object*)(l_Lean_Expr_cheapBetaReduce_cont___closed__1));
v___x_11_ = ((lean_object*)(l_Lean_Expr_cheapBetaReduce_cont___closed__0));
v___x_12_ = l_mkPanicMessageWithDecl(v___x_11_, v___x_10_, v___x_9_, v___x_8_, v___x_7_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_cont(lean_object* v_e_13_, lean_object* v_args_14_, lean_object* v_i_15_, lean_object* v_fn_16_){
_start:
{
uint8_t v___x_17_; 
v___x_17_ = l_Lean_Expr_hasLooseBVars(v_fn_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; lean_object* v___x_19_; 
v___x_18_ = lean_array_get_size(v_args_14_);
v___x_19_ = l_Lean_mkAppRange(v_fn_16_, v_i_15_, v___x_18_, v_args_14_);
return v___x_19_;
}
else
{
if (lean_obj_tag(v_fn_16_) == 0)
{
lean_object* v_deBruijnIndex_20_; uint8_t v___x_21_; 
v_deBruijnIndex_20_ = lean_ctor_get(v_fn_16_, 0);
lean_inc(v_deBruijnIndex_20_);
lean_dec_ref(v_fn_16_);
v___x_21_ = lean_nat_dec_lt(v_deBruijnIndex_20_, v_i_15_);
if (v___x_21_ == 0)
{
lean_object* v___x_22_; lean_object* v___x_23_; 
lean_dec(v_deBruijnIndex_20_);
lean_dec(v_i_15_);
v___x_22_ = lean_obj_once(&l_Lean_Expr_cheapBetaReduce_cont___closed__3, &l_Lean_Expr_cheapBetaReduce_cont___closed__3_once, _init_l_Lean_Expr_cheapBetaReduce_cont___closed__3);
v___x_23_ = l_panic___at___00Lean_Expr_cheapBetaReduce_cont_spec__0(v___x_22_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v___x_24_ = l_Lean_instInhabitedExpr;
v___x_25_ = lean_nat_sub(v_i_15_, v_deBruijnIndex_20_);
lean_dec(v_deBruijnIndex_20_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_sub(v___x_25_, v___x_26_);
lean_dec(v___x_25_);
v___x_28_ = lean_array_get_borrowed(v___x_24_, v_args_14_, v___x_27_);
lean_dec(v___x_27_);
v___x_29_ = lean_array_get_size(v_args_14_);
lean_inc(v___x_28_);
v___x_30_ = l_Lean_mkAppRange(v___x_28_, v_i_15_, v___x_29_, v_args_14_);
return v___x_30_;
}
}
else
{
lean_dec_ref(v_fn_16_);
lean_dec(v_i_15_);
lean_inc_ref(v_e_13_);
return v_e_13_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_cont___boxed(lean_object* v_e_31_, lean_object* v_args_32_, lean_object* v_i_33_, lean_object* v_fn_34_){
_start:
{
lean_object* v_res_35_; 
v_res_35_ = l_Lean_Expr_cheapBetaReduce_cont(v_e_31_, v_args_32_, v_i_33_, v_fn_34_);
lean_dec_ref(v_args_32_);
lean_dec_ref(v_e_31_);
return v_res_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_loop(lean_object* v_e_36_, lean_object* v_args_37_, lean_object* v_i_38_, lean_object* v_fn_39_){
_start:
{
lean_object* v___x_40_; uint8_t v___x_41_; 
v___x_40_ = lean_array_get_size(v_args_37_);
v___x_41_ = lean_nat_dec_lt(v_i_38_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; 
v___x_42_ = l_Lean_Expr_cheapBetaReduce_cont(v_e_36_, v_args_37_, v_i_38_, v_fn_39_);
return v___x_42_;
}
else
{
if (lean_obj_tag(v_fn_39_) == 6)
{
lean_object* v_body_43_; lean_object* v___x_44_; lean_object* v___x_45_; 
v_body_43_ = lean_ctor_get(v_fn_39_, 2);
lean_inc_ref(v_body_43_);
lean_dec_ref(v_fn_39_);
v___x_44_ = lean_unsigned_to_nat(1u);
v___x_45_ = lean_nat_add(v_i_38_, v___x_44_);
lean_dec(v_i_38_);
v_i_38_ = v___x_45_;
v_fn_39_ = v_body_43_;
goto _start;
}
else
{
lean_object* v___x_47_; 
v___x_47_ = l_Lean_Expr_cheapBetaReduce_cont(v_e_36_, v_args_37_, v_i_38_, v_fn_39_);
return v___x_47_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce_loop___boxed(lean_object* v_e_48_, lean_object* v_args_49_, lean_object* v_i_50_, lean_object* v_fn_51_){
_start:
{
lean_object* v_res_52_; 
v_res_52_ = l_Lean_Expr_cheapBetaReduce_loop(v_e_48_, v_args_49_, v_i_50_, v_fn_51_);
lean_dec_ref(v_args_49_);
lean_dec_ref(v_e_48_);
return v_res_52_;
}
}
static lean_object* _init_l_Lean_Expr_cheapBetaReduce___closed__0(void){
_start:
{
lean_object* v___x_53_; lean_object* v_dummy_54_; 
v___x_53_ = lean_box(0);
v_dummy_54_ = l_Lean_Expr_sort___override(v___x_53_);
return v_dummy_54_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_cheapBetaReduce(lean_object* v_e_55_){
_start:
{
uint8_t v___x_56_; 
v___x_56_ = l_Lean_Expr_isApp(v_e_55_);
if (v___x_56_ == 0)
{
return v_e_55_;
}
else
{
lean_object* v_fn_57_; uint8_t v___x_58_; 
v_fn_57_ = l_Lean_Expr_getAppFn(v_e_55_);
v___x_58_ = l_Lean_Expr_isLambda(v_fn_57_);
if (v___x_58_ == 0)
{
lean_dec_ref(v_fn_57_);
return v_e_55_;
}
else
{
lean_object* v_dummy_59_; lean_object* v_nargs_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v_args_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v_dummy_59_ = lean_obj_once(&l_Lean_Expr_cheapBetaReduce___closed__0, &l_Lean_Expr_cheapBetaReduce___closed__0_once, _init_l_Lean_Expr_cheapBetaReduce___closed__0);
v_nargs_60_ = l_Lean_Expr_getAppNumArgs(v_e_55_);
lean_inc(v_nargs_60_);
v___x_61_ = lean_mk_array(v_nargs_60_, v_dummy_59_);
v___x_62_ = lean_unsigned_to_nat(1u);
v___x_63_ = lean_nat_sub(v_nargs_60_, v___x_62_);
lean_dec(v_nargs_60_);
lean_inc_ref(v_e_55_);
v_args_64_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_55_, v___x_61_, v___x_63_);
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = l_Lean_Expr_cheapBetaReduce_loop(v_e_55_, v_args_64_, v___x_65_, v_fn_57_);
lean_dec_ref(v_args_64_);
lean_dec_ref(v_e_55_);
return v___x_66_;
}
}
}
}
lean_object* runtime_initialize_Lean_Expr(uint8_t builtin);
lean_object* runtime_initialize_Lean_LocalContext(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_InstantiateLevelParams(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Instantiate(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Util_InstantiateLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Instantiate(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Expr(uint8_t builtin);
lean_object* initialize_Lean_LocalContext(uint8_t builtin);
lean_object* initialize_Lean_Util_InstantiateLevelParams(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Instantiate(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_LocalContext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_InstantiateLevelParams(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Instantiate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Instantiate(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Instantiate(builtin);
}
#ifdef __cplusplus
}
#endif
