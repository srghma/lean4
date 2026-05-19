// Lean compiler output
// Module: Lean.Kernel.List
// Imports: public import Init.Data.List.Basic
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
LEAN_EXPORT uint8_t l_List_all2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_all2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all2___redArg(lean_object* v_R_1_, lean_object* v_x_2_, lean_object* v_x_3_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_dec_ref(v_R_1_);
if (lean_obj_tag(v_x_3_) == 0)
{
uint8_t v___x_4_; 
v___x_4_ = 1;
return v___x_4_;
}
else
{
uint8_t v___x_5_; 
lean_dec_ref(v_x_3_);
v___x_5_ = 0;
return v___x_5_;
}
}
else
{
if (lean_obj_tag(v_x_3_) == 0)
{
uint8_t v___x_6_; 
lean_dec_ref(v_x_2_);
lean_dec_ref(v_R_1_);
v___x_6_ = 0;
return v___x_6_;
}
else
{
lean_object* v_head_7_; lean_object* v_tail_8_; lean_object* v_head_9_; lean_object* v_tail_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_head_7_ = lean_ctor_get(v_x_2_, 0);
lean_inc(v_head_7_);
v_tail_8_ = lean_ctor_get(v_x_2_, 1);
lean_inc(v_tail_8_);
lean_dec_ref(v_x_2_);
v_head_9_ = lean_ctor_get(v_x_3_, 0);
lean_inc(v_head_9_);
v_tail_10_ = lean_ctor_get(v_x_3_, 1);
lean_inc(v_tail_10_);
lean_dec_ref(v_x_3_);
lean_inc_ref(v_R_1_);
v___x_11_ = lean_apply_2(v_R_1_, v_head_7_, v_head_9_);
v___x_12_ = lean_unbox(v___x_11_);
if (v___x_12_ == 0)
{
uint8_t v___x_13_; 
lean_dec(v_tail_10_);
lean_dec(v_tail_8_);
lean_dec_ref(v_R_1_);
v___x_13_ = lean_unbox(v___x_11_);
return v___x_13_;
}
else
{
v_x_2_ = v_tail_8_;
v_x_3_ = v_tail_10_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_all2___redArg___boxed(lean_object* v_R_15_, lean_object* v_x_16_, lean_object* v_x_17_){
_start:
{
uint8_t v_res_18_; lean_object* v_r_19_; 
v_res_18_ = l_List_all2___redArg(v_R_15_, v_x_16_, v_x_17_);
v_r_19_ = lean_box(v_res_18_);
return v_r_19_;
}
}
LEAN_EXPORT uint8_t l_List_all2(lean_object* v_00_u03b1_20_, lean_object* v_R_21_, lean_object* v_x_22_, lean_object* v_x_23_){
_start:
{
uint8_t v___x_24_; 
v___x_24_ = l_List_all2___redArg(v_R_21_, v_x_22_, v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_List_all2___boxed(lean_object* v_00_u03b1_25_, lean_object* v_R_26_, lean_object* v_x_27_, lean_object* v_x_28_){
_start:
{
uint8_t v_res_29_; lean_object* v_r_30_; 
v_res_29_ = l_List_all2(v_00_u03b1_25_, v_R_26_, v_x_27_, v_x_28_);
v_r_30_ = lean_box(v_res_29_);
return v_r_30_;
}
}
lean_object* runtime_initialize_Init_Data_List_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_List(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_List(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_List_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_List(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_List(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_List(builtin);
}
#ifdef __cplusplus
}
#endif
