// Lean compiler output
// Module: Lean.Kernel.PtrEq
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
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqExpr_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqExpr_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Kernel_ptrEqExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_ptrEqExpr___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqConstantInfo_unsafe__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqConstantInfo_unsafe__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Kernel_ptrEqConstantInfo(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Kernel_ptrEqConstantInfo___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqExpr_unsafe__1(lean_object* v_a_1_, lean_object* v_b_2_){
_start:
{
size_t v___x_3_; size_t v___x_4_; uint8_t v___x_5_; 
v___x_3_ = lean_ptr_addr(v_a_1_);
v___x_4_ = lean_ptr_addr(v_b_2_);
v___x_5_ = lean_usize_dec_eq(v___x_3_, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqExpr_unsafe__1___boxed(lean_object* v_a_6_, lean_object* v_b_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqExpr_unsafe__1(v_a_6_, v_b_7_);
lean_dec_ref(v_b_7_);
lean_dec_ref(v_a_6_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_Lean_Kernel_ptrEqExpr(lean_object* v_a_10_, lean_object* v_b_11_){
_start:
{
uint8_t v___x_12_; 
v___x_12_ = l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqExpr_unsafe__1(v_a_10_, v_b_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_ptrEqExpr___boxed(lean_object* v_a_13_, lean_object* v_b_14_){
_start:
{
uint8_t v_res_15_; lean_object* v_r_16_; 
v_res_15_ = l_Lean_Kernel_ptrEqExpr(v_a_13_, v_b_14_);
lean_dec_ref(v_b_14_);
lean_dec_ref(v_a_13_);
v_r_16_ = lean_box(v_res_15_);
return v_r_16_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqConstantInfo_unsafe__1(lean_object* v_a_17_, lean_object* v_b_18_){
_start:
{
size_t v___x_19_; size_t v___x_20_; uint8_t v___x_21_; 
v___x_19_ = lean_ptr_addr(v_a_17_);
v___x_20_ = lean_ptr_addr(v_b_18_);
v___x_21_ = lean_usize_dec_eq(v___x_19_, v___x_20_);
return v___x_21_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqConstantInfo_unsafe__1___boxed(lean_object* v_a_22_, lean_object* v_b_23_){
_start:
{
uint8_t v_res_24_; lean_object* v_r_25_; 
v_res_24_ = l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqConstantInfo_unsafe__1(v_a_22_, v_b_23_);
lean_dec_ref(v_b_23_);
lean_dec_ref(v_a_22_);
v_r_25_ = lean_box(v_res_24_);
return v_r_25_;
}
}
LEAN_EXPORT uint8_t l_Lean_Kernel_ptrEqConstantInfo(lean_object* v_a_26_, lean_object* v_b_27_){
_start:
{
uint8_t v___x_28_; 
v___x_28_ = l___private_Lean_Kernel_PtrEq_0__Lean_Kernel_ptrEqConstantInfo_unsafe__1(v_a_26_, v_b_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_ptrEqConstantInfo___boxed(lean_object* v_a_29_, lean_object* v_b_30_){
_start:
{
uint8_t v_res_31_; lean_object* v_r_32_; 
v_res_31_ = l_Lean_Kernel_ptrEqConstantInfo(v_a_29_, v_b_30_);
lean_dec_ref(v_b_30_);
lean_dec_ref(v_a_29_);
v_r_32_ = lean_box(v_res_31_);
return v_r_32_;
}
}
lean_object* runtime_initialize_Lean_Declaration(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_PtrEq(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_PtrEq(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Declaration(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_PtrEq(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Declaration(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_PtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_PtrEq(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_PtrEq(builtin);
}
#ifdef __cplusplus
}
#endif
