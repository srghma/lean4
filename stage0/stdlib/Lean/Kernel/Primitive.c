// Lean compiler output
// Module: Lean.Kernel.Primitive
// Imports: public import Lean.Kernel.TypeChecker
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
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveDef___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveDef(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveDef___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean4Lean_Environment_checkPrimitiveInductive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean4Lean_Environment_checkPrimitiveInductive___closed__0 = (const lean_object*)&l_Lean4Lean_Environment_checkPrimitiveInductive___closed__0_value;
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveInductive(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveDef___redArg(lean_object* v_a_1_){
_start:
{
uint8_t v___x_2_; lean_object* v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; 
v___x_2_ = 0;
v___x_3_ = lean_box(v___x_2_);
v___x_4_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4_, 0, v___x_3_);
lean_ctor_set(v___x_4_, 1, v_a_1_);
v___x_5_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5_, 0, v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveDef(lean_object* v___v_6_, lean_object* v_a_7_, lean_object* v_a_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean4Lean_Environment_checkPrimitiveDef___redArg(v_a_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveDef___boxed(lean_object* v___v_10_, lean_object* v_a_11_, lean_object* v_a_12_){
_start:
{
lean_object* v_res_13_; 
v_res_13_ = l_Lean4Lean_Environment_checkPrimitiveDef(v___v_10_, v_a_11_, v_a_12_);
lean_dec_ref(v_a_11_);
lean_dec_ref(v___v_10_);
return v_res_13_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveInductive(lean_object* v___env_17_, lean_object* v___lparams_18_, lean_object* v___nparams_19_, lean_object* v___types_20_, uint8_t v___isUnsafe_21_){
_start:
{
lean_object* v___x_22_; 
v___x_22_ = ((lean_object*)(l_Lean4Lean_Environment_checkPrimitiveInductive___closed__0));
return v___x_22_;
}
}
LEAN_EXPORT lean_object* l_Lean4Lean_Environment_checkPrimitiveInductive___boxed(lean_object* v___env_23_, lean_object* v___lparams_24_, lean_object* v___nparams_25_, lean_object* v___types_26_, lean_object* v___isUnsafe_27_){
_start:
{
uint8_t v___isUnsafe_boxed_28_; lean_object* v_res_29_; 
v___isUnsafe_boxed_28_ = lean_unbox(v___isUnsafe_27_);
v_res_29_ = l_Lean4Lean_Environment_checkPrimitiveInductive(v___env_23_, v___lparams_24_, v___nparams_25_, v___types_26_, v___isUnsafe_boxed_28_);
lean_dec(v___types_26_);
lean_dec(v___nparams_25_);
lean_dec(v___lparams_24_);
lean_dec_ref(v___env_23_);
return v_res_29_;
}
}
lean_object* runtime_initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Kernel_Primitive(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Kernel_Primitive(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Kernel_TypeChecker(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Kernel_Primitive(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Kernel_TypeChecker(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Kernel_Primitive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Kernel_Primitive(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Kernel_Primitive(builtin);
}
#ifdef __cplusplus
}
#endif
