// Lean compiler output
// Module: Lean.Kernel.Declaration
// Imports: public import Lean.Declaration
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
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_lt_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_lt_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_ReducibilityHints_lt_x27(lean_object* v_x_1_, lean_object* v_x_2_){
_start:
{
switch(lean_obj_tag(v_x_2_))
{
case 0:
{
uint8_t v___x_3_; 
v___x_3_ = 0;
return v___x_3_;
}
case 1:
{
switch(lean_obj_tag(v_x_1_))
{
case 1:
{
uint8_t v___x_4_; 
v___x_4_ = 0;
return v___x_4_;
}
case 0:
{
uint8_t v___x_5_; 
v___x_5_ = 1;
return v___x_5_;
}
default: 
{
uint8_t v___x_6_; 
v___x_6_ = 1;
return v___x_6_;
}
}
}
default: 
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
uint8_t v___x_7_; 
v___x_7_ = 1;
return v___x_7_;
}
case 1:
{
uint8_t v___x_8_; 
v___x_8_ = 0;
return v___x_8_;
}
default: 
{
uint32_t v_a_9_; uint32_t v_a_10_; uint8_t v___x_11_; 
v_a_9_ = lean_ctor_get_uint32(v_x_2_, 0);
v_a_10_ = lean_ctor_get_uint32(v_x_1_, 0);
v___x_11_ = lean_uint32_dec_lt(v_a_10_, v_a_9_);
return v___x_11_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ReducibilityHints_lt_x27___boxed(lean_object* v_x_12_, lean_object* v_x_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_ReducibilityHints_lt_x27(v_x_12_, v_x_13_);
lean_dec(v_x_13_);
lean_dec(v_x_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Declaration(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Declaration(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Declaration(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Declaration(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Declaration(builtin);
}
#ifdef __cplusplus
}
#endif
