// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.FieldNormNum
// Imports: Lean.Meta.Basic Init.Grind.FieldNormNum Lean.Meta.Tactic.Grind.SynthInstance Lean.Meta.AppBuilder Lean.Meta.LitValues Lean.Util.SafeExponentiation
use crate::ffi::{
    lean_array_push, lean_int_dec_eq, lean_int_dec_le, lean_int_neg,
    lean_mk_empty_array_with_capacity, lean_nat_abs, lean_nat_dec_eq, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Rat::Basic::{
    l_Rat_add, l_Rat_div___boxed, l_Rat_inv, l_Rat_mul___boxed, l_Rat_neg, l_Rat_ofInt, l_Rat_pow,
    l_Rat_sub, l_Rat_zpow,
};
use crate::r#gen::Init::Grind::FieldNormNum::{
    initialize_Init_Grind_FieldNormNum, runtime_initialize_Init_Grind_FieldNormNum,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Exception::l_Lean_Exception_isInterrupt;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_const___override, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_eagerReflBoolTrue, l_Lean_mkApp3, l_Lean_mkApp6, l_Lean_mkApp7, l_Lean_mkApp8,
    l_Lean_mkApp9, l_Lean_mkAppB, l_Lean_mkConst, l_Lean_mkIntLit, l_Lean_mkNatLit,
};
use crate::r#gen::Lean::Level::l_Lean_Level_ofNat;
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppM, l_Lean_Meta_mkAppOptM, l_Lean_Meta_mkMul,
    runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_isDefEqI, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Check::l_Lean_Meta_checkWithKernel;
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_getDecLevel_x3f;
use crate::r#gen::Lean::Meta::LitValues::{
    initialize_Lean_Meta_LitValues, l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
    runtime_initialize_Lean_Meta_LitValues,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::ToExpr::{l_Lean_instToExprInt_mkNat, l_Lean_instToExprRat_mkInt};
use crate::r#gen::Lean::Util::SafeExponentiation::{
    initialize_Lean_Util_SafeExponentiation, l_Lean_checkExponent,
    runtime_initialize_Lean_Util_SafeExponentiation,
};
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__4_value) as *mut leanh::LeanObject,884698968996596991 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 111, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__6_value) as *mut leanh::LeanObject,16367934121419604941 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__7_value) as *mut leanh::LeanObject,12221341192526463479 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value) as *mut leanh::LeanObject,10806710915646349764 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__10_value) as *mut leanh::LeanObject,14047490016268445595 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 115, 67, 104, 97, 114, 80, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__12_value) as *mut leanh::LeanObject,5319903737885873089 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__0_value) as *mut leanh::LeanObject,9594062259507646949 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__3_value) as *mut leanh::LeanObject,5442360487226035463 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__0_value) as *mut leanh::LeanObject,18134279130838690737 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__2_value) as *mut leanh::LeanObject,7102027102192867304 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__0_value) as *mut leanh::LeanObject,10135981711945425184 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value) as *mut leanh::LeanObject,10806710915646349764 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__2_value) as *mut leanh::LeanObject,18169824201013588232 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [105, 110, 115, 116, 72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__0_value) as *mut leanh::LeanObject,1334142589224437282 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__2_value) as *mut leanh::LeanObject,1566421737999521813 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value) as *mut leanh::LeanObject,10806710915646349764 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__0_value) as *mut leanh::LeanObject,10040236838748678500 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__0_value) as *mut leanh::LeanObject,7723290638220826725 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [110, 112, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__0_value) as *mut leanh::LeanObject,18388652353510661091 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 112, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__0_value) as *mut leanh::LeanObject,12479433955753450565 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value) as *mut leanh::LeanObject,9341924117480681831 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__2_value) as *mut leanh::LeanObject,12050285396929189622 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value) as *mut leanh::LeanObject,14765357657372582228 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__0_value) as *mut leanh::LeanObject,5779414593499529281 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__0_value) as *mut leanh::LeanObject,7063772860359172143 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__9_value) as *mut leanh::LeanObject,10806710915646349764 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value) as *mut leanh::LeanObject,14561037289535094017 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 110, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__0_value) as *mut leanh::LeanObject,4977321555018234431 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__0_value) as *mut leanh::LeanObject,4463466624472370110 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__0_value) as *mut leanh::LeanObject,11858238400308895562 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__1_value) as *mut leanh::LeanObject,6100819061652633370 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [82, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value) as *mut leanh::LeanObject,3708748166848919527 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [105, 110, 115, 116, 68, 105, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__8_value) as *mut leanh::LeanObject,3708748166848919527 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__12_value) as *mut leanh::LeanObject,16847769216878551944 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__0_value) as *mut leanh::LeanObject,17636616155771105671 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__0_value) as *mut leanh::LeanObject,15578568367168711682 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [105, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__2_value) as *mut leanh::LeanObject,1412621069384631438 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__3_value) as *mut leanh::LeanObject,10171450186735820607 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__5_value) as *mut leanh::LeanObject,9626815015619986526 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__6_value) as *mut leanh::LeanObject,17185717442815859305 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 80, 111, 119, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__8_value) as *mut leanh::LeanObject,12847922472053947547 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__9_value) as *mut leanh::LeanObject,10422657989269798688 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__11_value) as *mut leanh::LeanObject,16856108565602861689 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__12_value) as *mut leanh::LeanObject,4187025665268973031 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__14_value) as *mut leanh::LeanObject,2929883540436775422 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__15_value) as *mut leanh::LeanObject,1611444129324655608 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__17_value) as *mut leanh::LeanObject,10393083817453678557 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__18_value) as *mut leanh::LeanObject,10680564408669940870 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Rat_add as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 111, 114, 109, 78, 117, 109, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [97, 100, 100, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__22_value) as *mut leanh::LeanObject,741401208331177623 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Rat_mul___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 117, 108, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__25_value) as *mut leanh::LeanObject,10641486155849465736 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Rat_sub as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 117, 98, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__28_value) as *mut leanh::LeanObject,14662498971446321666 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Rat_div___boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 105, 118, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__31_value) as *mut leanh::LeanObject,14548913076287177137 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [122, 112, 111, 119, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__33_value) as *mut leanh::LeanObject,1238242381894674172 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value) as *mut leanh::LeanObject,7009148538150066493 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 115, 116, 78, 101, 103, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__37_value) as *mut leanh::LeanObject,7009148538150066493 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__40_value) as *mut leanh::LeanObject,6362876895233142233 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 112, 111, 119, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__43_value) as *mut leanh::LeanObject,5631726294731202597 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Rat_neg as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [110, 101, 103, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__46_value) as *mut leanh::LeanObject,18165027133106165507 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Rat_inv as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 118, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__49_value) as *mut leanh::LeanObject,289188182952354560 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [111, 102, 78, 97, 116, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__51_value) as *mut leanh::LeanObject,15437953856677429896 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [110, 97, 116, 67, 97, 115, 116, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__53_value) as *mut leanh::LeanObject,8492160332077194357 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [105, 110, 116, 67, 97, 115, 116, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__55_value) as *mut leanh::LeanObject,5241300462083217438 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [101, 113, 95, 109, 117, 108, 95, 105, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__1_value)
            as *mut leanh::LeanObject,
        8581820632374574150 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 95, 105, 110, 118, 0],
};
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__3_value)
            as *mut leanh::LeanObject,
        1986008386857775227 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [101, 113, 95, 105, 110, 116, 0],
};
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__1_value) as *mut leanh::LeanObject,13563742693681136756 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__2_value) as *mut leanh::LeanObject,8615353994042975301 as *mut leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__21_value) as *mut leanh::LeanObject,8658793402349085690 as *mut leanh::LeanObject] };
pub static l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__5_value)
            as *mut leanh::LeanObject,
        11206211019692506773 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2397_ = leanh::lean_unsigned_to_nat(0);
    v___x_2398_ = l_Lean_mkNatLit(v___x_2397_);
    return v___x_2398_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(
    mut v_type_2399_: *mut leanh::LeanObject,
    mut v_x_2400_: *mut leanh::LeanObject,
    mut v_a_2401_: *mut leanh::LeanObject,
    mut v_a_2402_: *mut leanh::LeanObject,
    mut v_a_2403_: *mut leanh::LeanObject,
    mut v_a_2404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v_val_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v_val_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2441_: u8 = 0;
    let mut v_val_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2449_: u8 = 0;
    let mut v_a_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v___x_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2457_: u8 = 0;
    let mut v_a_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2461_: u8 = 0;
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2465_: u8 = 0;
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2470_: u8 = 0;
    let mut v_a_2471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2474_: u8 = 0;
    let mut v___x_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2478_: u8 = 0;
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2483_: u8 = 0;
    let mut v_a_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2487_: u8 = 0;
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2491_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_type_2399_);
                v___x_2406_ = l_Lean_Meta_getDecLevel_x3f(
                    v_type_2399_,
                    v_a_2401_,
                    v_a_2402_,
                    v_a_2403_,
                    v_a_2404_,
                );
                if leanh::lean_obj_tag(v___x_2406_) == 0 {
                    v_a_2407_ = leanh::lean_ctor_get(v___x_2406_, 0);
                    v_isSharedCheck_2483_ = (!leanh::lean_is_exclusive(v___x_2406_)) as u8;
                    if v_isSharedCheck_2483_ == 0 {
                        v___x_2409_ = v___x_2406_;
                        v_isShared_2410_ = v_isSharedCheck_2483_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2407_);
                        leanh::lean_dec(v___x_2406_);
                        v___x_2409_ = leanh::lean_box(0);
                        v_isShared_2410_ = v_isSharedCheck_2483_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_x_2400_);
                    leanh::lean_dec_ref(v_type_2399_);
                    v_a_2484_ = leanh::lean_ctor_get(v___x_2406_, 0);
                    v_isSharedCheck_2491_ = (!leanh::lean_is_exclusive(v___x_2406_)) as u8;
                    if v_isSharedCheck_2491_ == 0 {
                        v___x_2486_ = v___x_2406_;
                        v_isShared_2487_ = v_isSharedCheck_2491_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2484_);
                        leanh::lean_dec(v___x_2406_);
                        v___x_2486_ = leanh::lean_box(0);
                        v_isShared_2487_ = v_isSharedCheck_2491_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_2407_) == 1 {
                    leanh::lean_del_object(v___x_2409_);
                    v_val_2411_ = leanh::lean_ctor_get(v_a_2407_, 0);
                    leanh::lean_inc_n(v_val_2411_, 2);
                    leanh::lean_dec_ref_known(v_a_2407_, 1);
                    v___x_2412_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__3;
                    v___x_2413_ = leanh::lean_box(0);
                    v___x_2414_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2414_, 0, v_val_2411_);
                    leanh::lean_ctor_set(v___x_2414_, 1, v___x_2413_);
                    leanh::lean_inc_ref(v___x_2414_);
                    v___x_2415_ = l_Lean_mkConst(v___x_2412_, v___x_2414_);
                    leanh::lean_inc_ref(v_type_2399_);
                    v___x_2416_ = l_Lean_Expr_app___override(v___x_2415_, v_type_2399_);
                    v___x_2417_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2416_,
                        v_a_2401_,
                        v_a_2402_,
                        v_a_2403_,
                        v_a_2404_,
                    );
                    if leanh::lean_obj_tag(v___x_2417_) == 0 {
                        v_a_2418_ = leanh::lean_ctor_get(v___x_2417_, 0);
                        v_isSharedCheck_2470_ =
                            (!leanh::lean_is_exclusive(v___x_2417_)) as u8;
                        if v_isSharedCheck_2470_ == 0 {
                            v___x_2420_ = v___x_2417_;
                            v_isShared_2421_ = v_isSharedCheck_2470_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2418_);
                            leanh::lean_dec(v___x_2417_);
                            v___x_2420_ = leanh::lean_box(0);
                            v_isShared_2421_ = v_isSharedCheck_2470_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref_known(v___x_2414_, 2);
                        leanh::lean_dec(v_val_2411_);
                        leanh::lean_dec_ref(v_x_2400_);
                        leanh::lean_dec_ref(v_type_2399_);
                        v_a_2471_ = leanh::lean_ctor_get(v___x_2417_, 0);
                        v_isSharedCheck_2478_ =
                            (!leanh::lean_is_exclusive(v___x_2417_)) as u8;
                        if v_isSharedCheck_2478_ == 0 {
                            v___x_2473_ = v___x_2417_;
                            v_isShared_2474_ = v_isSharedCheck_2478_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2471_);
                            leanh::lean_dec(v___x_2417_);
                            v___x_2473_ = leanh::lean_box(0);
                            v_isShared_2474_ = v_isSharedCheck_2478_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2407_);
                    leanh::lean_dec_ref(v_x_2400_);
                    leanh::lean_dec_ref(v_type_2399_);
                    v___x_2479_ = leanh::lean_box(0);
                    if v_isShared_2410_ == 0 {
                        leanh::lean_ctor_set(v___x_2409_, 0, v___x_2479_);
                        v___x_2481_ = v___x_2409_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2482_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2482_, 0, v___x_2479_);
                        v___x_2481_ = v_reuseFailAlloc_2482_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_2418_) == 1 {
                    leanh::lean_del_object(v___x_2420_);
                    v_val_2422_ = leanh::lean_ctor_get(v_a_2418_, 0);
                    leanh::lean_inc_n(v_val_2422_, 2);
                    leanh::lean_dec_ref_known(v_a_2418_, 1);
                    v___x_2423_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__5;
                    leanh::lean_inc_ref_n(v___x_2414_, 3);
                    v___x_2424_ = l_Lean_mkConst(v___x_2423_, v___x_2414_);
                    leanh::lean_inc_ref_n(v_type_2399_, 4);
                    v___x_2425_ = l_Lean_mkAppB(v___x_2424_, v_type_2399_, v_val_2422_);
                    v___x_2426_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__8;
                    v___x_2427_ = l_Lean_mkConst(v___x_2426_, v___x_2414_);
                    v___x_2428_ = l_Lean_mkAppB(v___x_2427_, v_type_2399_, v___x_2425_);
                    v___x_2429_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__11;
                    v___x_2430_ = l_Lean_mkConst(v___x_2429_, v___x_2414_);
                    leanh::lean_inc_ref(v___x_2428_);
                    v___x_2431_ = l_Lean_mkAppB(v___x_2430_, v_type_2399_, v___x_2428_);
                    v___x_2432_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__13;
                    v___x_2433_ = l_Lean_mkConst(v___x_2432_, v___x_2414_);
                    v___x_2434_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___closed__14);
                    leanh::lean_inc_ref(v___x_2431_);
                    v___x_2435_ =
                        l_Lean_mkApp3(v___x_2433_, v_type_2399_, v___x_2431_, v___x_2434_);
                    leanh::lean_inc_ref(v___x_2435_);
                    v___x_2436_ = l_Lean_Meta_checkWithKernel(
                        v___x_2435_,
                        v_a_2401_,
                        v_a_2402_,
                        v_a_2403_,
                        v_a_2404_,
                    );
                    if leanh::lean_obj_tag(v___x_2436_) == 0 {
                        leanh::lean_dec_ref_known(v___x_2436_, 1);
                        v___x_2437_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                            v___x_2435_,
                            v_a_2401_,
                            v_a_2402_,
                            v_a_2403_,
                            v_a_2404_,
                        );
                        if leanh::lean_obj_tag(v___x_2437_) == 0 {
                            v_a_2438_ = leanh::lean_ctor_get(v___x_2437_, 0);
                            v_isSharedCheck_2449_ =
                                (!leanh::lean_is_exclusive(v___x_2437_)) as u8;
                            if v_isSharedCheck_2449_ == 0 {
                                v___x_2440_ = v___x_2437_;
                                v_isShared_2441_ = v_isSharedCheck_2449_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2438_);
                                leanh::lean_dec(v___x_2437_);
                                v___x_2440_ = leanh::lean_box(0);
                                v_isShared_2441_ = v_isSharedCheck_2449_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_2431_);
                            leanh::lean_dec_ref(v___x_2428_);
                            leanh::lean_dec(v_val_2422_);
                            leanh::lean_dec(v_val_2411_);
                            leanh::lean_dec_ref(v_x_2400_);
                            leanh::lean_dec_ref(v_type_2399_);
                            v_a_2450_ = leanh::lean_ctor_get(v___x_2437_, 0);
                            v_isSharedCheck_2457_ =
                                (!leanh::lean_is_exclusive(v___x_2437_)) as u8;
                            if v_isSharedCheck_2457_ == 0 {
                                v___x_2452_ = v___x_2437_;
                                v_isShared_2453_ = v_isSharedCheck_2457_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_2450_);
                                leanh::lean_dec(v___x_2437_);
                                v___x_2452_ = leanh::lean_box(0);
                                v_isShared_2453_ = v_isSharedCheck_2457_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2435_);
                        leanh::lean_dec_ref(v___x_2431_);
                        leanh::lean_dec_ref(v___x_2428_);
                        leanh::lean_dec(v_val_2422_);
                        leanh::lean_dec(v_val_2411_);
                        leanh::lean_dec_ref(v_x_2400_);
                        leanh::lean_dec_ref(v_type_2399_);
                        v_a_2458_ = leanh::lean_ctor_get(v___x_2436_, 0);
                        v_isSharedCheck_2465_ =
                            (!leanh::lean_is_exclusive(v___x_2436_)) as u8;
                        if v_isSharedCheck_2465_ == 0 {
                            v___x_2460_ = v___x_2436_;
                            v_isShared_2461_ = v_isSharedCheck_2465_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_2458_);
                            leanh::lean_dec(v___x_2436_);
                            v___x_2460_ = leanh::lean_box(0);
                            v_isShared_2461_ = v_isSharedCheck_2465_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_2418_);
                    leanh::lean_dec_ref_known(v___x_2414_, 2);
                    leanh::lean_dec(v_val_2411_);
                    leanh::lean_dec_ref(v_x_2400_);
                    leanh::lean_dec_ref(v_type_2399_);
                    v___x_2466_ = leanh::lean_box(0);
                    if v_isShared_2421_ == 0 {
                        leanh::lean_ctor_set(v___x_2420_, 0, v___x_2466_);
                        v___x_2468_ = v___x_2420_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2466_);
                        v___x_2468_ = v_reuseFailAlloc_2469_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_2438_) == 1 {
                    leanh::lean_del_object(v___x_2440_);
                    v_val_2442_ = leanh::lean_ctor_get(v_a_2438_, 0);
                    leanh::lean_inc(v_val_2442_);
                    leanh::lean_dec_ref_known(v_a_2438_, 1);
                    v___x_2443_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v___x_2443_, 0, v_val_2411_);
                    leanh::lean_ctor_set(v___x_2443_, 1, v_type_2399_);
                    leanh::lean_ctor_set(v___x_2443_, 2, v_val_2422_);
                    leanh::lean_ctor_set(v___x_2443_, 3, v_val_2442_);
                    leanh::lean_ctor_set(v___x_2443_, 4, v___x_2428_);
                    leanh::lean_ctor_set(v___x_2443_, 5, v___x_2431_);
                    leanh::lean_inc(v_a_2404_);
                    leanh::lean_inc_ref(v_a_2403_);
                    leanh::lean_inc(v_a_2402_);
                    leanh::lean_inc_ref(v_a_2401_);
                    v___x_2444_ = leanh::lean_apply_6(
                        v_x_2400_,
                        v___x_2443_,
                        v_a_2401_,
                        v_a_2402_,
                        v_a_2403_,
                        v_a_2404_,
                        leanh::lean_box(0),
                    );
                    return v___x_2444_;
                } else {
                    leanh::lean_dec(v_a_2438_);
                    leanh::lean_dec_ref(v___x_2431_);
                    leanh::lean_dec_ref(v___x_2428_);
                    leanh::lean_dec(v_val_2422_);
                    leanh::lean_dec(v_val_2411_);
                    leanh::lean_dec_ref(v_x_2400_);
                    leanh::lean_dec_ref(v_type_2399_);
                    v___x_2445_ = leanh::lean_box(0);
                    if v_isShared_2441_ == 0 {
                        leanh::lean_ctor_set(v___x_2440_, 0, v___x_2445_);
                        v___x_2447_ = v___x_2440_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2448_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2448_, 0, v___x_2445_);
                        v___x_2447_ = v_reuseFailAlloc_2448_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2447_;
            }
            5 => {
                if v_isShared_2453_ == 0 {
                    v___x_2455_ = v___x_2452_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2456_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_a_2450_);
                    v___x_2455_ = v_reuseFailAlloc_2456_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2455_;
            }
            7 => {
                if v_isShared_2461_ == 0 {
                    v___x_2463_ = v___x_2460_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2464_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
                    v___x_2463_ = v_reuseFailAlloc_2464_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2463_;
            }
            9 => {
                return v___x_2468_;
            }
            10 => {
                if v_isShared_2474_ == 0 {
                    v___x_2476_ = v___x_2473_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
                    v___x_2476_ = v_reuseFailAlloc_2477_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2476_;
            }
            12 => {
                return v___x_2481_;
            }
            13 => {
                if v_isShared_2487_ == 0 {
                    v___x_2489_ = v___x_2486_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2490_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
                    v___x_2489_ = v_reuseFailAlloc_2490_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2489_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg___boxed(
    mut v_type_2492_: *mut leanh::LeanObject,
    mut v_x_2493_: *mut leanh::LeanObject,
    mut v_a_2494_: *mut leanh::LeanObject,
    mut v_a_2495_: *mut leanh::LeanObject,
    mut v_a_2496_: *mut leanh::LeanObject,
    mut v_a_2497_: *mut leanh::LeanObject,
    mut v_a_2498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2499_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2492_, v_x_2493_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
    leanh::lean_dec(v_a_2497_);
    leanh::lean_dec_ref(v_a_2496_);
    leanh::lean_dec(v_a_2495_);
    leanh::lean_dec_ref(v_a_2494_);
    return v_res_2499_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(
    mut v_00_u03b1_2500_: *mut leanh::LeanObject,
    mut v_type_2501_: *mut leanh::LeanObject,
    mut v_x_2502_: *mut leanh::LeanObject,
    mut v_a_2503_: *mut leanh::LeanObject,
    mut v_a_2504_: *mut leanh::LeanObject,
    mut v_a_2505_: *mut leanh::LeanObject,
    mut v_a_2506_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2508_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_2501_, v_x_2502_, v_a_2503_, v_a_2504_, v_a_2505_, v_a_2506_);
    return v___x_2508_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___boxed(
    mut v_00_u03b1_2509_: *mut leanh::LeanObject,
    mut v_type_2510_: *mut leanh::LeanObject,
    mut v_x_2511_: *mut leanh::LeanObject,
    mut v_a_2512_: *mut leanh::LeanObject,
    mut v_a_2513_: *mut leanh::LeanObject,
    mut v_a_2514_: *mut leanh::LeanObject,
    mut v_a_2515_: *mut leanh::LeanObject,
    mut v_a_2516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2517_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f(v_00_u03b1_2509_, v_type_2510_, v_x_2511_, v_a_2512_, v_a_2513_, v_a_2514_, v_a_2515_);
    leanh::lean_dec(v_a_2515_);
    leanh::lean_dec_ref(v_a_2514_);
    leanh::lean_dec(v_a_2513_);
    leanh::lean_dec_ref(v_a_2512_);
    return v_res_2517_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(
    mut v_inst_2528_: *mut leanh::LeanObject,
    mut v_a_2529_: *mut leanh::LeanObject,
    mut v_a_2530_: *mut leanh::LeanObject,
    mut v_a_2531_: *mut leanh::LeanObject,
    mut v_a_2532_: *mut leanh::LeanObject,
    mut v_a_2533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2555_: u8 = 0;
    let mut v_a_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v___x_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2535_ = leanh::lean_ctor_get(v_a_2529_, 0);
                v_type_2536_ = leanh::lean_ctor_get(v_a_2529_, 1);
                v_semiringInst_2537_ = leanh::lean_ctor_get(v_a_2529_, 5);
                v___x_2538_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__1;
                v___x_2539_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2535_);
                v___x_2540_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2540_, 0, v_u_2535_);
                leanh::lean_ctor_set(v___x_2540_, 1, v___x_2539_);
                leanh::lean_inc_ref(v___x_2540_);
                v___x_2541_ = l_Lean_mkConst(v___x_2538_, v___x_2540_);
                v___x_2542_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___closed__4;
                v___x_2543_ = l_Lean_mkConst(v___x_2542_, v___x_2540_);
                leanh::lean_inc_ref(v_semiringInst_2537_);
                leanh::lean_inc_ref_n(v_type_2536_, 2);
                v___x_2544_ = l_Lean_mkAppB(v___x_2543_, v_type_2536_, v_semiringInst_2537_);
                v___x_2545_ = l_Lean_mkAppB(v___x_2541_, v_type_2536_, v___x_2544_);
                v___x_2546_ = l_Lean_Meta_isDefEqI(
                    v_inst_2528_,
                    v___x_2545_,
                    v_a_2530_,
                    v_a_2531_,
                    v_a_2532_,
                    v_a_2533_,
                );
                if leanh::lean_obj_tag(v___x_2546_) == 0 {
                    v_a_2547_ = leanh::lean_ctor_get(v___x_2546_, 0);
                    v_isSharedCheck_2555_ = (!leanh::lean_is_exclusive(v___x_2546_)) as u8;
                    if v_isSharedCheck_2555_ == 0 {
                        v___x_2549_ = v___x_2546_;
                        v_isShared_2550_ = v_isSharedCheck_2555_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2547_);
                        leanh::lean_dec(v___x_2546_);
                        v___x_2549_ = leanh::lean_box(0);
                        v_isShared_2550_ = v_isSharedCheck_2555_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2556_ = leanh::lean_ctor_get(v___x_2546_, 0);
                    v_isSharedCheck_2563_ = (!leanh::lean_is_exclusive(v___x_2546_)) as u8;
                    if v_isSharedCheck_2563_ == 0 {
                        v___x_2558_ = v___x_2546_;
                        v_isShared_2559_ = v_isSharedCheck_2563_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2556_);
                        leanh::lean_dec(v___x_2546_);
                        v___x_2558_ = leanh::lean_box(0);
                        v_isShared_2559_ = v_isSharedCheck_2563_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2551_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2551_, 0, v_a_2547_);
                if v_isShared_2550_ == 0 {
                    leanh::lean_ctor_set(v___x_2549_, 0, v___x_2551_);
                    v___x_2553_ = v___x_2549_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2554_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2554_, 0, v___x_2551_);
                    v___x_2553_ = v_reuseFailAlloc_2554_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2553_;
            }
            3 => {
                if v_isShared_2559_ == 0 {
                    v___x_2561_ = v___x_2558_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_a_2556_);
                    v___x_2561_ = v_reuseFailAlloc_2562_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2561_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst___boxed(
    mut v_inst_2564_: *mut leanh::LeanObject,
    mut v_a_2565_: *mut leanh::LeanObject,
    mut v_a_2566_: *mut leanh::LeanObject,
    mut v_a_2567_: *mut leanh::LeanObject,
    mut v_a_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
    mut v_a_2570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2571_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_inst_2564_, v_a_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
    leanh::lean_dec(v_a_2569_);
    leanh::lean_dec_ref(v_a_2568_);
    leanh::lean_dec(v_a_2567_);
    leanh::lean_dec_ref(v_a_2566_);
    leanh::lean_dec_ref(v_a_2565_);
    return v_res_2571_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(
    mut v_inst_2581_: *mut leanh::LeanObject,
    mut v_a_2582_: *mut leanh::LeanObject,
    mut v_a_2583_: *mut leanh::LeanObject,
    mut v_a_2584_: *mut leanh::LeanObject,
    mut v_a_2585_: *mut leanh::LeanObject,
    mut v_a_2586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2608_: u8 = 0;
    let mut v_a_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2588_ = leanh::lean_ctor_get(v_a_2582_, 0);
                v_type_2589_ = leanh::lean_ctor_get(v_a_2582_, 1);
                v_semiringInst_2590_ = leanh::lean_ctor_get(v_a_2582_, 5);
                v___x_2591_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__1;
                v___x_2592_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2588_);
                v___x_2593_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2593_, 0, v_u_2588_);
                leanh::lean_ctor_set(v___x_2593_, 1, v___x_2592_);
                leanh::lean_inc_ref(v___x_2593_);
                v___x_2594_ = l_Lean_mkConst(v___x_2591_, v___x_2593_);
                v___x_2595_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___closed__3;
                v___x_2596_ = l_Lean_mkConst(v___x_2595_, v___x_2593_);
                leanh::lean_inc_ref(v_semiringInst_2590_);
                leanh::lean_inc_ref_n(v_type_2589_, 2);
                v___x_2597_ = l_Lean_mkAppB(v___x_2596_, v_type_2589_, v_semiringInst_2590_);
                v___x_2598_ = l_Lean_mkAppB(v___x_2594_, v_type_2589_, v___x_2597_);
                v___x_2599_ = l_Lean_Meta_isDefEqI(
                    v_inst_2581_,
                    v___x_2598_,
                    v_a_2583_,
                    v_a_2584_,
                    v_a_2585_,
                    v_a_2586_,
                );
                if leanh::lean_obj_tag(v___x_2599_) == 0 {
                    v_a_2600_ = leanh::lean_ctor_get(v___x_2599_, 0);
                    v_isSharedCheck_2608_ = (!leanh::lean_is_exclusive(v___x_2599_)) as u8;
                    if v_isSharedCheck_2608_ == 0 {
                        v___x_2602_ = v___x_2599_;
                        v_isShared_2603_ = v_isSharedCheck_2608_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2600_);
                        leanh::lean_dec(v___x_2599_);
                        v___x_2602_ = leanh::lean_box(0);
                        v_isShared_2603_ = v_isSharedCheck_2608_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2609_ = leanh::lean_ctor_get(v___x_2599_, 0);
                    v_isSharedCheck_2616_ = (!leanh::lean_is_exclusive(v___x_2599_)) as u8;
                    if v_isSharedCheck_2616_ == 0 {
                        v___x_2611_ = v___x_2599_;
                        v_isShared_2612_ = v_isSharedCheck_2616_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2609_);
                        leanh::lean_dec(v___x_2599_);
                        v___x_2611_ = leanh::lean_box(0);
                        v_isShared_2612_ = v_isSharedCheck_2616_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2604_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2604_, 0, v_a_2600_);
                if v_isShared_2603_ == 0 {
                    leanh::lean_ctor_set(v___x_2602_, 0, v___x_2604_);
                    v___x_2606_ = v___x_2602_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2607_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
                    v___x_2606_ = v_reuseFailAlloc_2607_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2606_;
            }
            3 => {
                if v_isShared_2612_ == 0 {
                    v___x_2614_ = v___x_2611_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2615_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
                    v___x_2614_ = v_reuseFailAlloc_2615_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst___boxed(
    mut v_inst_2617_: *mut leanh::LeanObject,
    mut v_a_2618_: *mut leanh::LeanObject,
    mut v_a_2619_: *mut leanh::LeanObject,
    mut v_a_2620_: *mut leanh::LeanObject,
    mut v_a_2621_: *mut leanh::LeanObject,
    mut v_a_2622_: *mut leanh::LeanObject,
    mut v_a_2623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2624_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_inst_2617_, v_a_2618_, v_a_2619_, v_a_2620_, v_a_2621_, v_a_2622_);
    leanh::lean_dec(v_a_2622_);
    leanh::lean_dec_ref(v_a_2621_);
    leanh::lean_dec(v_a_2620_);
    leanh::lean_dec_ref(v_a_2619_);
    leanh::lean_dec_ref(v_a_2618_);
    return v_res_2624_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(
    mut v_inst_2634_: *mut leanh::LeanObject,
    mut v_a_2635_: *mut leanh::LeanObject,
    mut v_a_2636_: *mut leanh::LeanObject,
    mut v_a_2637_: *mut leanh::LeanObject,
    mut v_a_2638_: *mut leanh::LeanObject,
    mut v_a_2639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2656_: u8 = 0;
    let mut v___x_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2661_: u8 = 0;
    let mut v_a_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2665_: u8 = 0;
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2641_ = leanh::lean_ctor_get(v_a_2635_, 0);
                v_type_2642_ = leanh::lean_ctor_get(v_a_2635_, 1);
                v_ringInst_2643_ = leanh::lean_ctor_get(v_a_2635_, 4);
                v___x_2644_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__1;
                v___x_2645_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2641_);
                v___x_2646_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2646_, 0, v_u_2641_);
                leanh::lean_ctor_set(v___x_2646_, 1, v___x_2645_);
                leanh::lean_inc_ref(v___x_2646_);
                v___x_2647_ = l_Lean_mkConst(v___x_2644_, v___x_2646_);
                v___x_2648_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___closed__3;
                v___x_2649_ = l_Lean_mkConst(v___x_2648_, v___x_2646_);
                leanh::lean_inc_ref(v_ringInst_2643_);
                leanh::lean_inc_ref_n(v_type_2642_, 2);
                v___x_2650_ = l_Lean_mkAppB(v___x_2649_, v_type_2642_, v_ringInst_2643_);
                v___x_2651_ = l_Lean_mkAppB(v___x_2647_, v_type_2642_, v___x_2650_);
                v___x_2652_ = l_Lean_Meta_isDefEqI(
                    v_inst_2634_,
                    v___x_2651_,
                    v_a_2636_,
                    v_a_2637_,
                    v_a_2638_,
                    v_a_2639_,
                );
                if leanh::lean_obj_tag(v___x_2652_) == 0 {
                    v_a_2653_ = leanh::lean_ctor_get(v___x_2652_, 0);
                    v_isSharedCheck_2661_ = (!leanh::lean_is_exclusive(v___x_2652_)) as u8;
                    if v_isSharedCheck_2661_ == 0 {
                        v___x_2655_ = v___x_2652_;
                        v_isShared_2656_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2653_);
                        leanh::lean_dec(v___x_2652_);
                        v___x_2655_ = leanh::lean_box(0);
                        v_isShared_2656_ = v_isSharedCheck_2661_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2662_ = leanh::lean_ctor_get(v___x_2652_, 0);
                    v_isSharedCheck_2669_ = (!leanh::lean_is_exclusive(v___x_2652_)) as u8;
                    if v_isSharedCheck_2669_ == 0 {
                        v___x_2664_ = v___x_2652_;
                        v_isShared_2665_ = v_isSharedCheck_2669_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2662_);
                        leanh::lean_dec(v___x_2652_);
                        v___x_2664_ = leanh::lean_box(0);
                        v_isShared_2665_ = v_isSharedCheck_2669_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2657_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2657_, 0, v_a_2653_);
                if v_isShared_2656_ == 0 {
                    leanh::lean_ctor_set(v___x_2655_, 0, v___x_2657_);
                    v___x_2659_ = v___x_2655_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2660_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2660_, 0, v___x_2657_);
                    v___x_2659_ = v_reuseFailAlloc_2660_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2659_;
            }
            3 => {
                if v_isShared_2665_ == 0 {
                    v___x_2667_ = v___x_2664_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
                    v___x_2667_ = v_reuseFailAlloc_2668_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2667_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst___boxed(
    mut v_inst_2670_: *mut leanh::LeanObject,
    mut v_a_2671_: *mut leanh::LeanObject,
    mut v_a_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
    mut v_a_2675_: *mut leanh::LeanObject,
    mut v_a_2676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2677_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_inst_2670_, v_a_2671_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
    leanh::lean_dec(v_a_2675_);
    leanh::lean_dec_ref(v_a_2674_);
    leanh::lean_dec(v_a_2673_);
    leanh::lean_dec_ref(v_a_2672_);
    leanh::lean_dec_ref(v_a_2671_);
    return v_res_2677_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(
    mut v_inst_2687_: *mut leanh::LeanObject,
    mut v_a_2688_: *mut leanh::LeanObject,
    mut v_a_2689_: *mut leanh::LeanObject,
    mut v_a_2690_: *mut leanh::LeanObject,
    mut v_a_2691_: *mut leanh::LeanObject,
    mut v_a_2692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2714_: u8 = 0;
    let mut v_a_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2718_: u8 = 0;
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2694_ = leanh::lean_ctor_get(v_a_2688_, 0);
                v_type_2695_ = leanh::lean_ctor_get(v_a_2688_, 1);
                v_fieldInst_2696_ = leanh::lean_ctor_get(v_a_2688_, 2);
                v___x_2697_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1;
                v___x_2698_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2694_);
                v___x_2699_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2699_, 0, v_u_2694_);
                leanh::lean_ctor_set(v___x_2699_, 1, v___x_2698_);
                leanh::lean_inc_ref(v___x_2699_);
                v___x_2700_ = l_Lean_mkConst(v___x_2697_, v___x_2699_);
                v___x_2701_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__3;
                v___x_2702_ = l_Lean_mkConst(v___x_2701_, v___x_2699_);
                leanh::lean_inc_ref(v_fieldInst_2696_);
                leanh::lean_inc_ref_n(v_type_2695_, 2);
                v___x_2703_ = l_Lean_mkAppB(v___x_2702_, v_type_2695_, v_fieldInst_2696_);
                v___x_2704_ = l_Lean_mkAppB(v___x_2700_, v_type_2695_, v___x_2703_);
                v___x_2705_ = l_Lean_Meta_isDefEqI(
                    v_inst_2687_,
                    v___x_2704_,
                    v_a_2689_,
                    v_a_2690_,
                    v_a_2691_,
                    v_a_2692_,
                );
                if leanh::lean_obj_tag(v___x_2705_) == 0 {
                    v_a_2706_ = leanh::lean_ctor_get(v___x_2705_, 0);
                    v_isSharedCheck_2714_ = (!leanh::lean_is_exclusive(v___x_2705_)) as u8;
                    if v_isSharedCheck_2714_ == 0 {
                        v___x_2708_ = v___x_2705_;
                        v_isShared_2709_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2706_);
                        leanh::lean_dec(v___x_2705_);
                        v___x_2708_ = leanh::lean_box(0);
                        v_isShared_2709_ = v_isSharedCheck_2714_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2715_ = leanh::lean_ctor_get(v___x_2705_, 0);
                    v_isSharedCheck_2722_ = (!leanh::lean_is_exclusive(v___x_2705_)) as u8;
                    if v_isSharedCheck_2722_ == 0 {
                        v___x_2717_ = v___x_2705_;
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2715_);
                        leanh::lean_dec(v___x_2705_);
                        v___x_2717_ = leanh::lean_box(0);
                        v_isShared_2718_ = v_isSharedCheck_2722_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2710_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2710_, 0, v_a_2706_);
                if v_isShared_2709_ == 0 {
                    leanh::lean_ctor_set(v___x_2708_, 0, v___x_2710_);
                    v___x_2712_ = v___x_2708_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2713_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2713_, 0, v___x_2710_);
                    v___x_2712_ = v_reuseFailAlloc_2713_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2712_;
            }
            3 => {
                if v_isShared_2718_ == 0 {
                    v___x_2720_ = v___x_2717_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2721_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
                    v___x_2720_ = v_reuseFailAlloc_2721_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2720_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___boxed(
    mut v_inst_2723_: *mut leanh::LeanObject,
    mut v_a_2724_: *mut leanh::LeanObject,
    mut v_a_2725_: *mut leanh::LeanObject,
    mut v_a_2726_: *mut leanh::LeanObject,
    mut v_a_2727_: *mut leanh::LeanObject,
    mut v_a_2728_: *mut leanh::LeanObject,
    mut v_a_2729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2730_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_inst_2723_, v_a_2724_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_);
    leanh::lean_dec(v_a_2728_);
    leanh::lean_dec_ref(v_a_2727_);
    leanh::lean_dec(v_a_2726_);
    leanh::lean_dec_ref(v_a_2725_);
    leanh::lean_dec_ref(v_a_2724_);
    return v_res_2730_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(
    mut v_inst_2737_: *mut leanh::LeanObject,
    mut v_a_2738_: *mut leanh::LeanObject,
    mut v_a_2739_: *mut leanh::LeanObject,
    mut v_a_2740_: *mut leanh::LeanObject,
    mut v_a_2741_: *mut leanh::LeanObject,
    mut v_a_2742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2761_: u8 = 0;
    let mut v_a_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2765_: u8 = 0;
    let mut v___x_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2744_ = leanh::lean_ctor_get(v_a_2738_, 0);
                v_type_2745_ = leanh::lean_ctor_get(v_a_2738_, 1);
                v_ringInst_2746_ = leanh::lean_ctor_get(v_a_2738_, 4);
                v___x_2747_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___closed__1;
                v___x_2748_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2744_);
                v___x_2749_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2749_, 0, v_u_2744_);
                leanh::lean_ctor_set(v___x_2749_, 1, v___x_2748_);
                v___x_2750_ = l_Lean_mkConst(v___x_2747_, v___x_2749_);
                leanh::lean_inc_ref(v_ringInst_2746_);
                leanh::lean_inc_ref(v_type_2745_);
                v___x_2751_ = l_Lean_mkAppB(v___x_2750_, v_type_2745_, v_ringInst_2746_);
                v___x_2752_ = l_Lean_Meta_isDefEqI(
                    v_inst_2737_,
                    v___x_2751_,
                    v_a_2739_,
                    v_a_2740_,
                    v_a_2741_,
                    v_a_2742_,
                );
                if leanh::lean_obj_tag(v___x_2752_) == 0 {
                    v_a_2753_ = leanh::lean_ctor_get(v___x_2752_, 0);
                    v_isSharedCheck_2761_ = (!leanh::lean_is_exclusive(v___x_2752_)) as u8;
                    if v_isSharedCheck_2761_ == 0 {
                        v___x_2755_ = v___x_2752_;
                        v_isShared_2756_ = v_isSharedCheck_2761_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2753_);
                        leanh::lean_dec(v___x_2752_);
                        v___x_2755_ = leanh::lean_box(0);
                        v_isShared_2756_ = v_isSharedCheck_2761_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2762_ = leanh::lean_ctor_get(v___x_2752_, 0);
                    v_isSharedCheck_2769_ = (!leanh::lean_is_exclusive(v___x_2752_)) as u8;
                    if v_isSharedCheck_2769_ == 0 {
                        v___x_2764_ = v___x_2752_;
                        v_isShared_2765_ = v_isSharedCheck_2769_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2762_);
                        leanh::lean_dec(v___x_2752_);
                        v___x_2764_ = leanh::lean_box(0);
                        v_isShared_2765_ = v_isSharedCheck_2769_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2757_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2757_, 0, v_a_2753_);
                if v_isShared_2756_ == 0 {
                    leanh::lean_ctor_set(v___x_2755_, 0, v___x_2757_);
                    v___x_2759_ = v___x_2755_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
                    v___x_2759_ = v_reuseFailAlloc_2760_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2759_;
            }
            3 => {
                if v_isShared_2765_ == 0 {
                    v___x_2767_ = v___x_2764_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2768_, 0, v_a_2762_);
                    v___x_2767_ = v_reuseFailAlloc_2768_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst___boxed(
    mut v_inst_2770_: *mut leanh::LeanObject,
    mut v_a_2771_: *mut leanh::LeanObject,
    mut v_a_2772_: *mut leanh::LeanObject,
    mut v_a_2773_: *mut leanh::LeanObject,
    mut v_a_2774_: *mut leanh::LeanObject,
    mut v_a_2775_: *mut leanh::LeanObject,
    mut v_a_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2777_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_inst_2770_, v_a_2771_, v_a_2772_, v_a_2773_, v_a_2774_, v_a_2775_);
    leanh::lean_dec(v_a_2775_);
    leanh::lean_dec_ref(v_a_2774_);
    leanh::lean_dec(v_a_2773_);
    leanh::lean_dec_ref(v_a_2772_);
    leanh::lean_dec_ref(v_a_2771_);
    return v_res_2777_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(
    mut v_inst_2784_: *mut leanh::LeanObject,
    mut v_a_2785_: *mut leanh::LeanObject,
    mut v_a_2786_: *mut leanh::LeanObject,
    mut v_a_2787_: *mut leanh::LeanObject,
    mut v_a_2788_: *mut leanh::LeanObject,
    mut v_a_2789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2808_: u8 = 0;
    let mut v_a_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2791_ = leanh::lean_ctor_get(v_a_2785_, 0);
                v_type_2792_ = leanh::lean_ctor_get(v_a_2785_, 1);
                v_fieldInst_2793_ = leanh::lean_ctor_get(v_a_2785_, 2);
                v___x_2794_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___closed__1;
                v___x_2795_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2791_);
                v___x_2796_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2796_, 0, v_u_2791_);
                leanh::lean_ctor_set(v___x_2796_, 1, v___x_2795_);
                v___x_2797_ = l_Lean_mkConst(v___x_2794_, v___x_2796_);
                leanh::lean_inc_ref(v_fieldInst_2793_);
                leanh::lean_inc_ref(v_type_2792_);
                v___x_2798_ = l_Lean_mkAppB(v___x_2797_, v_type_2792_, v_fieldInst_2793_);
                v___x_2799_ = l_Lean_Meta_isDefEqI(
                    v_inst_2784_,
                    v___x_2798_,
                    v_a_2786_,
                    v_a_2787_,
                    v_a_2788_,
                    v_a_2789_,
                );
                if leanh::lean_obj_tag(v___x_2799_) == 0 {
                    v_a_2800_ = leanh::lean_ctor_get(v___x_2799_, 0);
                    v_isSharedCheck_2808_ = (!leanh::lean_is_exclusive(v___x_2799_)) as u8;
                    if v_isSharedCheck_2808_ == 0 {
                        v___x_2802_ = v___x_2799_;
                        v_isShared_2803_ = v_isSharedCheck_2808_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2800_);
                        leanh::lean_dec(v___x_2799_);
                        v___x_2802_ = leanh::lean_box(0);
                        v_isShared_2803_ = v_isSharedCheck_2808_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2809_ = leanh::lean_ctor_get(v___x_2799_, 0);
                    v_isSharedCheck_2816_ = (!leanh::lean_is_exclusive(v___x_2799_)) as u8;
                    if v_isSharedCheck_2816_ == 0 {
                        v___x_2811_ = v___x_2799_;
                        v_isShared_2812_ = v_isSharedCheck_2816_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2809_);
                        leanh::lean_dec(v___x_2799_);
                        v___x_2811_ = leanh::lean_box(0);
                        v_isShared_2812_ = v_isSharedCheck_2816_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2804_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2804_, 0, v_a_2800_);
                if v_isShared_2803_ == 0 {
                    leanh::lean_ctor_set(v___x_2802_, 0, v___x_2804_);
                    v___x_2806_ = v___x_2802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2807_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2807_, 0, v___x_2804_);
                    v___x_2806_ = v_reuseFailAlloc_2807_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2806_;
            }
            3 => {
                if v_isShared_2812_ == 0 {
                    v___x_2814_ = v___x_2811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst___boxed(
    mut v_inst_2817_: *mut leanh::LeanObject,
    mut v_a_2818_: *mut leanh::LeanObject,
    mut v_a_2819_: *mut leanh::LeanObject,
    mut v_a_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
    mut v_a_2822_: *mut leanh::LeanObject,
    mut v_a_2823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2824_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_inst_2817_, v_a_2818_, v_a_2819_, v_a_2820_, v_a_2821_, v_a_2822_);
    leanh::lean_dec(v_a_2822_);
    leanh::lean_dec_ref(v_a_2821_);
    leanh::lean_dec(v_a_2820_);
    leanh::lean_dec_ref(v_a_2819_);
    leanh::lean_dec_ref(v_a_2818_);
    return v_res_2824_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(
    mut v_inst_2831_: *mut leanh::LeanObject,
    mut v_a_2832_: *mut leanh::LeanObject,
    mut v_a_2833_: *mut leanh::LeanObject,
    mut v_a_2834_: *mut leanh::LeanObject,
    mut v_a_2835_: *mut leanh::LeanObject,
    mut v_a_2836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2850_: u8 = 0;
    let mut v___x_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2855_: u8 = 0;
    let mut v_a_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2859_: u8 = 0;
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2838_ = leanh::lean_ctor_get(v_a_2832_, 0);
                v_type_2839_ = leanh::lean_ctor_get(v_a_2832_, 1);
                v_semiringInst_2840_ = leanh::lean_ctor_get(v_a_2832_, 5);
                v___x_2841_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___closed__1;
                v___x_2842_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2838_);
                v___x_2843_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2843_, 0, v_u_2838_);
                leanh::lean_ctor_set(v___x_2843_, 1, v___x_2842_);
                v___x_2844_ = l_Lean_mkConst(v___x_2841_, v___x_2843_);
                leanh::lean_inc_ref(v_semiringInst_2840_);
                leanh::lean_inc_ref(v_type_2839_);
                v___x_2845_ = l_Lean_mkAppB(v___x_2844_, v_type_2839_, v_semiringInst_2840_);
                v___x_2846_ = l_Lean_Meta_isDefEqI(
                    v_inst_2831_,
                    v___x_2845_,
                    v_a_2833_,
                    v_a_2834_,
                    v_a_2835_,
                    v_a_2836_,
                );
                if leanh::lean_obj_tag(v___x_2846_) == 0 {
                    v_a_2847_ = leanh::lean_ctor_get(v___x_2846_, 0);
                    v_isSharedCheck_2855_ = (!leanh::lean_is_exclusive(v___x_2846_)) as u8;
                    if v_isSharedCheck_2855_ == 0 {
                        v___x_2849_ = v___x_2846_;
                        v_isShared_2850_ = v_isSharedCheck_2855_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2847_);
                        leanh::lean_dec(v___x_2846_);
                        v___x_2849_ = leanh::lean_box(0);
                        v_isShared_2850_ = v_isSharedCheck_2855_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2856_ = leanh::lean_ctor_get(v___x_2846_, 0);
                    v_isSharedCheck_2863_ = (!leanh::lean_is_exclusive(v___x_2846_)) as u8;
                    if v_isSharedCheck_2863_ == 0 {
                        v___x_2858_ = v___x_2846_;
                        v_isShared_2859_ = v_isSharedCheck_2863_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2856_);
                        leanh::lean_dec(v___x_2846_);
                        v___x_2858_ = leanh::lean_box(0);
                        v_isShared_2859_ = v_isSharedCheck_2863_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2851_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2851_, 0, v_a_2847_);
                if v_isShared_2850_ == 0 {
                    leanh::lean_ctor_set(v___x_2849_, 0, v___x_2851_);
                    v___x_2853_ = v___x_2849_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2854_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2854_, 0, v___x_2851_);
                    v___x_2853_ = v_reuseFailAlloc_2854_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2853_;
            }
            3 => {
                if v_isShared_2859_ == 0 {
                    v___x_2861_ = v___x_2858_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst___boxed(
    mut v_inst_2864_: *mut leanh::LeanObject,
    mut v_a_2865_: *mut leanh::LeanObject,
    mut v_a_2866_: *mut leanh::LeanObject,
    mut v_a_2867_: *mut leanh::LeanObject,
    mut v_a_2868_: *mut leanh::LeanObject,
    mut v_a_2869_: *mut leanh::LeanObject,
    mut v_a_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2871_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_inst_2864_, v_a_2865_, v_a_2866_, v_a_2867_, v_a_2868_, v_a_2869_);
    leanh::lean_dec(v_a_2869_);
    leanh::lean_dec_ref(v_a_2868_);
    leanh::lean_dec(v_a_2867_);
    leanh::lean_dec_ref(v_a_2866_);
    leanh::lean_dec_ref(v_a_2865_);
    return v_res_2871_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(
    mut v_inst_2878_: *mut leanh::LeanObject,
    mut v_a_2879_: *mut leanh::LeanObject,
    mut v_a_2880_: *mut leanh::LeanObject,
    mut v_a_2881_: *mut leanh::LeanObject,
    mut v_a_2882_: *mut leanh::LeanObject,
    mut v_a_2883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2897_: u8 = 0;
    let mut v___x_2898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2902_: u8 = 0;
    let mut v_a_2903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2906_: u8 = 0;
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2885_ = leanh::lean_ctor_get(v_a_2879_, 0);
                v_type_2886_ = leanh::lean_ctor_get(v_a_2879_, 1);
                v_fieldInst_2887_ = leanh::lean_ctor_get(v_a_2879_, 2);
                v___x_2888_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___closed__1;
                v___x_2889_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2885_);
                v___x_2890_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2890_, 0, v_u_2885_);
                leanh::lean_ctor_set(v___x_2890_, 1, v___x_2889_);
                v___x_2891_ = l_Lean_mkConst(v___x_2888_, v___x_2890_);
                leanh::lean_inc_ref(v_fieldInst_2887_);
                leanh::lean_inc_ref(v_type_2886_);
                v___x_2892_ = l_Lean_mkAppB(v___x_2891_, v_type_2886_, v_fieldInst_2887_);
                v___x_2893_ = l_Lean_Meta_isDefEqI(
                    v_inst_2878_,
                    v___x_2892_,
                    v_a_2880_,
                    v_a_2881_,
                    v_a_2882_,
                    v_a_2883_,
                );
                if leanh::lean_obj_tag(v___x_2893_) == 0 {
                    v_a_2894_ = leanh::lean_ctor_get(v___x_2893_, 0);
                    v_isSharedCheck_2902_ = (!leanh::lean_is_exclusive(v___x_2893_)) as u8;
                    if v_isSharedCheck_2902_ == 0 {
                        v___x_2896_ = v___x_2893_;
                        v_isShared_2897_ = v_isSharedCheck_2902_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2894_);
                        leanh::lean_dec(v___x_2893_);
                        v___x_2896_ = leanh::lean_box(0);
                        v_isShared_2897_ = v_isSharedCheck_2902_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2903_ = leanh::lean_ctor_get(v___x_2893_, 0);
                    v_isSharedCheck_2910_ = (!leanh::lean_is_exclusive(v___x_2893_)) as u8;
                    if v_isSharedCheck_2910_ == 0 {
                        v___x_2905_ = v___x_2893_;
                        v_isShared_2906_ = v_isSharedCheck_2910_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2903_);
                        leanh::lean_dec(v___x_2893_);
                        v___x_2905_ = leanh::lean_box(0);
                        v_isShared_2906_ = v_isSharedCheck_2910_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2898_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2898_, 0, v_a_2894_);
                if v_isShared_2897_ == 0 {
                    leanh::lean_ctor_set(v___x_2896_, 0, v___x_2898_);
                    v___x_2900_ = v___x_2896_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2901_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
                    v___x_2900_ = v_reuseFailAlloc_2901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2900_;
            }
            3 => {
                if v_isShared_2906_ == 0 {
                    v___x_2908_ = v___x_2905_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2909_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
                    v___x_2908_ = v_reuseFailAlloc_2909_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst___boxed(
    mut v_inst_2911_: *mut leanh::LeanObject,
    mut v_a_2912_: *mut leanh::LeanObject,
    mut v_a_2913_: *mut leanh::LeanObject,
    mut v_a_2914_: *mut leanh::LeanObject,
    mut v_a_2915_: *mut leanh::LeanObject,
    mut v_a_2916_: *mut leanh::LeanObject,
    mut v_a_2917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2918_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_inst_2911_, v_a_2912_, v_a_2913_, v_a_2914_, v_a_2915_, v_a_2916_);
    leanh::lean_dec(v_a_2916_);
    leanh::lean_dec_ref(v_a_2915_);
    leanh::lean_dec(v_a_2914_);
    leanh::lean_dec_ref(v_a_2913_);
    leanh::lean_dec_ref(v_a_2912_);
    return v_res_2918_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(
    mut v_inst_2925_: *mut leanh::LeanObject,
    mut v_n_2926_: *mut leanh::LeanObject,
    mut v_a_2927_: *mut leanh::LeanObject,
    mut v_a_2928_: *mut leanh::LeanObject,
    mut v_a_2929_: *mut leanh::LeanObject,
    mut v_a_2930_: *mut leanh::LeanObject,
    mut v_a_2931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2945_: u8 = 0;
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut v_a_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2954_: u8 = 0;
    let mut v___x_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_2933_ = leanh::lean_ctor_get(v_a_2927_, 0);
                v_type_2934_ = leanh::lean_ctor_get(v_a_2927_, 1);
                v_semiringInst_2935_ = leanh::lean_ctor_get(v_a_2927_, 5);
                v___x_2936_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___closed__1;
                v___x_2937_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_2933_);
                v___x_2938_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2938_, 0, v_u_2933_);
                leanh::lean_ctor_set(v___x_2938_, 1, v___x_2937_);
                v___x_2939_ = l_Lean_mkConst(v___x_2936_, v___x_2938_);
                leanh::lean_inc_ref(v_semiringInst_2935_);
                leanh::lean_inc_ref(v_type_2934_);
                v___x_2940_ =
                    l_Lean_mkApp3(v___x_2939_, v_type_2934_, v_semiringInst_2935_, v_n_2926_);
                v___x_2941_ = l_Lean_Meta_isDefEqI(
                    v_inst_2925_,
                    v___x_2940_,
                    v_a_2928_,
                    v_a_2929_,
                    v_a_2930_,
                    v_a_2931_,
                );
                if leanh::lean_obj_tag(v___x_2941_) == 0 {
                    v_a_2942_ = leanh::lean_ctor_get(v___x_2941_, 0);
                    v_isSharedCheck_2950_ = (!leanh::lean_is_exclusive(v___x_2941_)) as u8;
                    if v_isSharedCheck_2950_ == 0 {
                        v___x_2944_ = v___x_2941_;
                        v_isShared_2945_ = v_isSharedCheck_2950_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2942_);
                        leanh::lean_dec(v___x_2941_);
                        v___x_2944_ = leanh::lean_box(0);
                        v_isShared_2945_ = v_isSharedCheck_2950_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2951_ = leanh::lean_ctor_get(v___x_2941_, 0);
                    v_isSharedCheck_2958_ = (!leanh::lean_is_exclusive(v___x_2941_)) as u8;
                    if v_isSharedCheck_2958_ == 0 {
                        v___x_2953_ = v___x_2941_;
                        v_isShared_2954_ = v_isSharedCheck_2958_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2951_);
                        leanh::lean_dec(v___x_2941_);
                        v___x_2953_ = leanh::lean_box(0);
                        v_isShared_2954_ = v_isSharedCheck_2958_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2946_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2946_, 0, v_a_2942_);
                if v_isShared_2945_ == 0 {
                    leanh::lean_ctor_set(v___x_2944_, 0, v___x_2946_);
                    v___x_2948_ = v___x_2944_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2949_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2946_);
                    v___x_2948_ = v_reuseFailAlloc_2949_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2948_;
            }
            3 => {
                if v_isShared_2954_ == 0 {
                    v___x_2956_ = v___x_2953_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2957_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
                    v___x_2956_ = v_reuseFailAlloc_2957_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst___boxed(
    mut v_inst_2959_: *mut leanh::LeanObject,
    mut v_n_2960_: *mut leanh::LeanObject,
    mut v_a_2961_: *mut leanh::LeanObject,
    mut v_a_2962_: *mut leanh::LeanObject,
    mut v_a_2963_: *mut leanh::LeanObject,
    mut v_a_2964_: *mut leanh::LeanObject,
    mut v_a_2965_: *mut leanh::LeanObject,
    mut v_a_2966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2967_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_inst_2959_, v_n_2960_, v_a_2961_, v_a_2962_, v_a_2963_, v_a_2964_, v_a_2965_);
    leanh::lean_dec(v_a_2965_);
    leanh::lean_dec_ref(v_a_2964_);
    leanh::lean_dec(v_a_2963_);
    leanh::lean_dec_ref(v_a_2962_);
    leanh::lean_dec_ref(v_a_2961_);
    return v_res_2967_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(
    mut v_a_2974_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_semiringInst_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_u_2976_ = leanh::lean_ctor_get(v_a_2974_, 0);
    v_type_2977_ = leanh::lean_ctor_get(v_a_2974_, 1);
    v_semiringInst_2978_ = leanh::lean_ctor_get(v_a_2974_, 5);
    v___x_2979_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___closed__1;
    v___x_2980_ = leanh::lean_box(0);
    leanh::lean_inc(v_u_2976_);
    v___x_2981_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2981_, 0, v_u_2976_);
    leanh::lean_ctor_set(v___x_2981_, 1, v___x_2980_);
    v___x_2982_ = l_Lean_mkConst(v___x_2979_, v___x_2981_);
    leanh::lean_inc_ref(v_semiringInst_2978_);
    leanh::lean_inc_ref(v_type_2977_);
    v___x_2983_ = l_Lean_mkAppB(v___x_2982_, v_type_2977_, v_semiringInst_2978_);
    v___x_2984_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    v___x_2985_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2985_, 0, v___x_2984_);
    return v___x_2985_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg___boxed(
    mut v_a_2986_: *mut leanh::LeanObject,
    mut v_a_2987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2988_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2988_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_2986_);
    leanh::lean_dec_ref(v_a_2986_);
    return v_res_2988_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(
    mut v_a_2989_: *mut leanh::LeanObject,
    mut v_a_2990_: *mut leanh::LeanObject,
    mut v_a_2991_: *mut leanh::LeanObject,
    mut v_a_2992_: *mut leanh::LeanObject,
    mut v_a_2993_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2995_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_2989_);
    return v___x_2995_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___boxed(
    mut v_a_2996_: *mut leanh::LeanObject,
    mut v_a_2997_: *mut leanh::LeanObject,
    mut v_a_2998_: *mut leanh::LeanObject,
    mut v_a_2999_: *mut leanh::LeanObject,
    mut v_a_3000_: *mut leanh::LeanObject,
    mut v_a_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3002_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst(v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_);
    leanh::lean_dec(v_a_3000_);
    leanh::lean_dec_ref(v_a_2999_);
    leanh::lean_dec(v_a_2998_);
    leanh::lean_dec_ref(v_a_2997_);
    leanh::lean_dec_ref(v_a_2996_);
    return v_res_3002_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(
    mut v_inst_3003_: *mut leanh::LeanObject,
    mut v_a_3004_: *mut leanh::LeanObject,
    mut v_a_3005_: *mut leanh::LeanObject,
    mut v_a_3006_: *mut leanh::LeanObject,
    mut v_a_3007_: *mut leanh::LeanObject,
    mut v_a_3008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v___x_3016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3020_: u8 = 0;
    let mut v___x_3022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3027_: u8 = 0;
    let mut v_a_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3031_: u8 = 0;
    let mut v___x_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3035_: u8 = 0;
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3010_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_3004_);
                v_a_3011_ = leanh::lean_ctor_get(v___x_3010_, 0);
                leanh::lean_inc(v_a_3011_);
                leanh::lean_dec_ref(v___x_3010_);
                v_val_3012_ = leanh::lean_ctor_get(v_a_3011_, 0);
                v_isSharedCheck_3036_ = (!leanh::lean_is_exclusive(v_a_3011_)) as u8;
                if v_isSharedCheck_3036_ == 0 {
                    v___x_3014_ = v_a_3011_;
                    v_isShared_3015_ = v_isSharedCheck_3036_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3012_);
                    leanh::lean_dec(v_a_3011_);
                    v___x_3014_ = leanh::lean_box(0);
                    v_isShared_3015_ = v_isSharedCheck_3036_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3016_ = l_Lean_Meta_isDefEqI(
                    v_inst_3003_,
                    v_val_3012_,
                    v_a_3005_,
                    v_a_3006_,
                    v_a_3007_,
                    v_a_3008_,
                );
                if leanh::lean_obj_tag(v___x_3016_) == 0 {
                    v_a_3017_ = leanh::lean_ctor_get(v___x_3016_, 0);
                    v_isSharedCheck_3027_ = (!leanh::lean_is_exclusive(v___x_3016_)) as u8;
                    if v_isSharedCheck_3027_ == 0 {
                        v___x_3019_ = v___x_3016_;
                        v_isShared_3020_ = v_isSharedCheck_3027_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3017_);
                        leanh::lean_dec(v___x_3016_);
                        v___x_3019_ = leanh::lean_box(0);
                        v_isShared_3020_ = v_isSharedCheck_3027_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3014_);
                    v_a_3028_ = leanh::lean_ctor_get(v___x_3016_, 0);
                    v_isSharedCheck_3035_ = (!leanh::lean_is_exclusive(v___x_3016_)) as u8;
                    if v_isSharedCheck_3035_ == 0 {
                        v___x_3030_ = v___x_3016_;
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3028_);
                        leanh::lean_dec(v___x_3016_);
                        v___x_3030_ = leanh::lean_box(0);
                        v_isShared_3031_ = v_isSharedCheck_3035_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3015_ == 0 {
                    leanh::lean_ctor_set(v___x_3014_, 0, v_a_3017_);
                    v___x_3022_ = v___x_3014_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3026_, 0, v_a_3017_);
                    v___x_3022_ = v_reuseFailAlloc_3026_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3020_ == 0 {
                    leanh::lean_ctor_set(v___x_3019_, 0, v___x_3022_);
                    v___x_3024_ = v___x_3019_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3025_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 0, v___x_3022_);
                    v___x_3024_ = v_reuseFailAlloc_3025_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3024_;
            }
            5 => {
                if v_isShared_3031_ == 0 {
                    v___x_3033_ = v___x_3030_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3034_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
                    v___x_3033_ = v_reuseFailAlloc_3034_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst___boxed(
    mut v_inst_3037_: *mut leanh::LeanObject,
    mut v_a_3038_: *mut leanh::LeanObject,
    mut v_a_3039_: *mut leanh::LeanObject,
    mut v_a_3040_: *mut leanh::LeanObject,
    mut v_a_3041_: *mut leanh::LeanObject,
    mut v_a_3042_: *mut leanh::LeanObject,
    mut v_a_3043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3044_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3044_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_inst_3037_, v_a_3038_, v_a_3039_, v_a_3040_, v_a_3041_, v_a_3042_);
    leanh::lean_dec(v_a_3042_);
    leanh::lean_dec_ref(v_a_3041_);
    leanh::lean_dec(v_a_3040_);
    leanh::lean_dec_ref(v_a_3039_);
    leanh::lean_dec_ref(v_a_3038_);
    return v_res_3044_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(
    mut v_n_3049_: *mut leanh::LeanObject,
    mut v_a_3050_: *mut leanh::LeanObject,
    mut v_a_3051_: *mut leanh::LeanObject,
    mut v_a_3052_: *mut leanh::LeanObject,
    mut v_a_3053_: *mut leanh::LeanObject,
    mut v_a_3054_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_3057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3077_: u8 = 0;
    let mut v___y_3079_: u8 = 0;
    let mut v___x_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: u8 = 0;
    let mut v___x_3091_: u8 = 0;
    let mut v_isSharedCheck_3092_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_3060_ = leanh::lean_ctor_get(v_a_3050_, 0);
                v_type_3061_ = leanh::lean_ctor_get(v_a_3050_, 1);
                v___x_3062_ = l_Lean_mkNatLit(v_n_3049_);
                v___x_3063_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1;
                leanh::lean_inc_ref(v_type_3061_);
                v___x_3064_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3064_, 0, v_type_3061_);
                v___x_3065_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_3062_);
                v___x_3066_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3066_, 0, v___x_3062_);
                v___x_3067_ = leanh::lean_unsigned_to_nat(3);
                v___x_3068_ = lean_mk_empty_array_with_capacity(v___x_3067_);
                v___x_3069_ = lean_array_push(v___x_3068_, v___x_3064_);
                v___x_3070_ = lean_array_push(v___x_3069_, v___x_3065_);
                v___x_3071_ = lean_array_push(v___x_3070_, v___x_3066_);
                v___x_3072_ = l_Lean_Meta_mkAppOptM(
                    v___x_3063_,
                    v___x_3071_,
                    v_a_3051_,
                    v_a_3052_,
                    v_a_3053_,
                    v_a_3054_,
                );
                if leanh::lean_obj_tag(v___x_3072_) == 0 {
                    leanh::lean_dec_ref(v___x_3062_);
                    v_a_3073_ = leanh::lean_ctor_get(v___x_3072_, 0);
                    leanh::lean_inc(v_a_3073_);
                    leanh::lean_dec_ref_known(v___x_3072_, 1);
                    v_r_3057_ = v_a_3073_;
                    state = 1;
                    continue;
                } else {
                    v_a_3074_ = leanh::lean_ctor_get(v___x_3072_, 0);
                    v_isSharedCheck_3092_ = (!leanh::lean_is_exclusive(v___x_3072_)) as u8;
                    if v_isSharedCheck_3092_ == 0 {
                        v___x_3076_ = v___x_3072_;
                        v_isShared_3077_ = v_isSharedCheck_3092_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3074_);
                        leanh::lean_dec(v___x_3072_);
                        v___x_3076_ = leanh::lean_box(0);
                        v_isShared_3077_ = v_isSharedCheck_3092_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3058_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3058_, 0, v_r_3057_);
                v___x_3059_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3059_, 0, v___x_3058_);
                return v___x_3059_;
            }
            2 => {
                v___x_3090_ = l_Lean_Exception_isInterrupt(v_a_3074_);
                if v___x_3090_ == 0 {
                    leanh::lean_inc(v_a_3074_);
                    v___x_3091_ = l_Lean_Exception_isRuntime(v_a_3074_);
                    v___y_3079_ = v___x_3091_;
                    state = 3;
                    continue;
                } else {
                    v___y_3079_ = v___x_3090_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_3079_ == 0 {
                    leanh::lean_del_object(v___x_3076_);
                    leanh::lean_dec(v_a_3074_);
                    v___x_3080_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCastInst___redArg(v_a_3050_);
                    v_a_3081_ = leanh::lean_ctor_get(v___x_3080_, 0);
                    leanh::lean_inc(v_a_3081_);
                    leanh::lean_dec_ref(v___x_3080_);
                    v_val_3082_ = leanh::lean_ctor_get(v_a_3081_, 0);
                    leanh::lean_inc(v_val_3082_);
                    leanh::lean_dec(v_a_3081_);
                    v___x_3083_ = leanh::lean_box(0);
                    leanh::lean_inc(v_u_3060_);
                    v___x_3084_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3084_, 0, v_u_3060_);
                    leanh::lean_ctor_set(v___x_3084_, 1, v___x_3083_);
                    v___x_3085_ = l_Lean_mkConst(v___x_3063_, v___x_3084_);
                    leanh::lean_inc_ref(v_type_3061_);
                    v___x_3086_ =
                        l_Lean_mkApp3(v___x_3085_, v_type_3061_, v_val_3082_, v___x_3062_);
                    v_r_3057_ = v___x_3086_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_3062_);
                    if v_isShared_3077_ == 0 {
                        v___x_3088_ = v___x_3076_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3089_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3089_, 0, v_a_3074_);
                        v___x_3088_ = v_reuseFailAlloc_3089_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3088_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___boxed(
    mut v_n_3093_: *mut leanh::LeanObject,
    mut v_a_3094_: *mut leanh::LeanObject,
    mut v_a_3095_: *mut leanh::LeanObject,
    mut v_a_3096_: *mut leanh::LeanObject,
    mut v_a_3097_: *mut leanh::LeanObject,
    mut v_a_3098_: *mut leanh::LeanObject,
    mut v_a_3099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3100_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_n_3093_, v_a_3094_, v_a_3095_, v_a_3096_, v_a_3097_, v_a_3098_);
    leanh::lean_dec(v_a_3098_);
    leanh::lean_dec_ref(v_a_3097_);
    leanh::lean_dec(v_a_3096_);
    leanh::lean_dec_ref(v_a_3095_);
    leanh::lean_dec_ref(v_a_3094_);
    return v_res_3100_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(
    mut v_a_3107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_u_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ringInst_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_u_3109_ = leanh::lean_ctor_get(v_a_3107_, 0);
    v_type_3110_ = leanh::lean_ctor_get(v_a_3107_, 1);
    v_ringInst_3111_ = leanh::lean_ctor_get(v_a_3107_, 4);
    v___x_3112_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___closed__1;
    v___x_3113_ = leanh::lean_box(0);
    leanh::lean_inc(v_u_3109_);
    v___x_3114_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3114_, 0, v_u_3109_);
    leanh::lean_ctor_set(v___x_3114_, 1, v___x_3113_);
    v___x_3115_ = l_Lean_mkConst(v___x_3112_, v___x_3114_);
    leanh::lean_inc_ref(v_ringInst_3111_);
    leanh::lean_inc_ref(v_type_3110_);
    v___x_3116_ = l_Lean_mkAppB(v___x_3115_, v_type_3110_, v_ringInst_3111_);
    v___x_3117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3117_, 0, v___x_3116_);
    v___x_3118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_3118_, 0, v___x_3117_);
    return v___x_3118_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg___boxed(
    mut v_a_3119_: *mut leanh::LeanObject,
    mut v_a_3120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3121_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_3119_);
    leanh::lean_dec_ref(v_a_3119_);
    return v_res_3121_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(
    mut v_a_3122_: *mut leanh::LeanObject,
    mut v_a_3123_: *mut leanh::LeanObject,
    mut v_a_3124_: *mut leanh::LeanObject,
    mut v_a_3125_: *mut leanh::LeanObject,
    mut v_a_3126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3128_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_3122_);
    return v___x_3128_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___boxed(
    mut v_a_3129_: *mut leanh::LeanObject,
    mut v_a_3130_: *mut leanh::LeanObject,
    mut v_a_3131_: *mut leanh::LeanObject,
    mut v_a_3132_: *mut leanh::LeanObject,
    mut v_a_3133_: *mut leanh::LeanObject,
    mut v_a_3134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3135_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst(v_a_3129_, v_a_3130_, v_a_3131_, v_a_3132_, v_a_3133_);
    leanh::lean_dec(v_a_3133_);
    leanh::lean_dec_ref(v_a_3132_);
    leanh::lean_dec(v_a_3131_);
    leanh::lean_dec_ref(v_a_3130_);
    leanh::lean_dec_ref(v_a_3129_);
    return v_res_3135_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(
    mut v_inst_3136_: *mut leanh::LeanObject,
    mut v_a_3137_: *mut leanh::LeanObject,
    mut v_a_3138_: *mut leanh::LeanObject,
    mut v_a_3139_: *mut leanh::LeanObject,
    mut v_a_3140_: *mut leanh::LeanObject,
    mut v_a_3141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3148_: u8 = 0;
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v___x_3155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut v_a_3161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3164_: u8 = 0;
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_isSharedCheck_3169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3143_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_3137_);
                v_a_3144_ = leanh::lean_ctor_get(v___x_3143_, 0);
                leanh::lean_inc(v_a_3144_);
                leanh::lean_dec_ref(v___x_3143_);
                v_val_3145_ = leanh::lean_ctor_get(v_a_3144_, 0);
                v_isSharedCheck_3169_ = (!leanh::lean_is_exclusive(v_a_3144_)) as u8;
                if v_isSharedCheck_3169_ == 0 {
                    v___x_3147_ = v_a_3144_;
                    v_isShared_3148_ = v_isSharedCheck_3169_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_val_3145_);
                    leanh::lean_dec(v_a_3144_);
                    v___x_3147_ = leanh::lean_box(0);
                    v_isShared_3148_ = v_isSharedCheck_3169_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3149_ = l_Lean_Meta_isDefEqI(
                    v_inst_3136_,
                    v_val_3145_,
                    v_a_3138_,
                    v_a_3139_,
                    v_a_3140_,
                    v_a_3141_,
                );
                if leanh::lean_obj_tag(v___x_3149_) == 0 {
                    v_a_3150_ = leanh::lean_ctor_get(v___x_3149_, 0);
                    v_isSharedCheck_3160_ = (!leanh::lean_is_exclusive(v___x_3149_)) as u8;
                    if v_isSharedCheck_3160_ == 0 {
                        v___x_3152_ = v___x_3149_;
                        v_isShared_3153_ = v_isSharedCheck_3160_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3150_);
                        leanh::lean_dec(v___x_3149_);
                        v___x_3152_ = leanh::lean_box(0);
                        v_isShared_3153_ = v_isSharedCheck_3160_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3147_);
                    v_a_3161_ = leanh::lean_ctor_get(v___x_3149_, 0);
                    v_isSharedCheck_3168_ = (!leanh::lean_is_exclusive(v___x_3149_)) as u8;
                    if v_isSharedCheck_3168_ == 0 {
                        v___x_3163_ = v___x_3149_;
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3161_);
                        leanh::lean_dec(v___x_3149_);
                        v___x_3163_ = leanh::lean_box(0);
                        v_isShared_3164_ = v_isSharedCheck_3168_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3148_ == 0 {
                    leanh::lean_ctor_set(v___x_3147_, 0, v_a_3150_);
                    v___x_3155_ = v___x_3147_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3159_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3159_, 0, v_a_3150_);
                    v___x_3155_ = v_reuseFailAlloc_3159_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3153_ == 0 {
                    leanh::lean_ctor_set(v___x_3152_, 0, v___x_3155_);
                    v___x_3157_ = v___x_3152_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3158_, 0, v___x_3155_);
                    v___x_3157_ = v_reuseFailAlloc_3158_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3157_;
            }
            5 => {
                if v_isShared_3164_ == 0 {
                    v___x_3166_ = v___x_3163_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3167_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
                    v___x_3166_ = v_reuseFailAlloc_3167_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst___boxed(
    mut v_inst_3170_: *mut leanh::LeanObject,
    mut v_a_3171_: *mut leanh::LeanObject,
    mut v_a_3172_: *mut leanh::LeanObject,
    mut v_a_3173_: *mut leanh::LeanObject,
    mut v_a_3174_: *mut leanh::LeanObject,
    mut v_a_3175_: *mut leanh::LeanObject,
    mut v_a_3176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3177_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_inst_3170_, v_a_3171_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
    leanh::lean_dec(v_a_3175_);
    leanh::lean_dec_ref(v_a_3174_);
    leanh::lean_dec(v_a_3173_);
    leanh::lean_dec_ref(v_a_3172_);
    leanh::lean_dec_ref(v_a_3171_);
    return v_res_3177_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(
    mut v_n_3182_: *mut leanh::LeanObject,
    mut v_a_3183_: *mut leanh::LeanObject,
    mut v_a_3184_: *mut leanh::LeanObject,
    mut v_a_3185_: *mut leanh::LeanObject,
    mut v_a_3186_: *mut leanh::LeanObject,
    mut v_a_3187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_r_3190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___y_3212_: u8 = 0;
    let mut v___x_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3223_: u8 = 0;
    let mut v___x_3224_: u8 = 0;
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_3193_ = leanh::lean_ctor_get(v_a_3183_, 0);
                v_type_3194_ = leanh::lean_ctor_get(v_a_3183_, 1);
                v___x_3195_ = l_Lean_mkIntLit(v_n_3182_);
                v___x_3196_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1;
                leanh::lean_inc_ref(v_type_3194_);
                v___x_3197_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3197_, 0, v_type_3194_);
                v___x_3198_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v___x_3195_);
                v___x_3199_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3199_, 0, v___x_3195_);
                v___x_3200_ = leanh::lean_unsigned_to_nat(3);
                v___x_3201_ = lean_mk_empty_array_with_capacity(v___x_3200_);
                v___x_3202_ = lean_array_push(v___x_3201_, v___x_3197_);
                v___x_3203_ = lean_array_push(v___x_3202_, v___x_3198_);
                v___x_3204_ = lean_array_push(v___x_3203_, v___x_3199_);
                v___x_3205_ = l_Lean_Meta_mkAppOptM(
                    v___x_3196_,
                    v___x_3204_,
                    v_a_3184_,
                    v_a_3185_,
                    v_a_3186_,
                    v_a_3187_,
                );
                if leanh::lean_obj_tag(v___x_3205_) == 0 {
                    leanh::lean_dec_ref(v___x_3195_);
                    v_a_3206_ = leanh::lean_ctor_get(v___x_3205_, 0);
                    leanh::lean_inc(v_a_3206_);
                    leanh::lean_dec_ref_known(v___x_3205_, 1);
                    v_r_3190_ = v_a_3206_;
                    state = 1;
                    continue;
                } else {
                    v_a_3207_ = leanh::lean_ctor_get(v___x_3205_, 0);
                    v_isSharedCheck_3225_ = (!leanh::lean_is_exclusive(v___x_3205_)) as u8;
                    if v_isSharedCheck_3225_ == 0 {
                        v___x_3209_ = v___x_3205_;
                        v_isShared_3210_ = v_isSharedCheck_3225_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3207_);
                        leanh::lean_dec(v___x_3205_);
                        v___x_3209_ = leanh::lean_box(0);
                        v_isShared_3210_ = v_isSharedCheck_3225_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3191_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3191_, 0, v_r_3190_);
                v___x_3192_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3192_, 0, v___x_3191_);
                return v___x_3192_;
            }
            2 => {
                v___x_3223_ = l_Lean_Exception_isInterrupt(v_a_3207_);
                if v___x_3223_ == 0 {
                    leanh::lean_inc(v_a_3207_);
                    v___x_3224_ = l_Lean_Exception_isRuntime(v_a_3207_);
                    v___y_3212_ = v___x_3224_;
                    state = 3;
                    continue;
                } else {
                    v___y_3212_ = v___x_3223_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v___y_3212_ == 0 {
                    leanh::lean_del_object(v___x_3209_);
                    leanh::lean_dec(v_a_3207_);
                    v___x_3213_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCastInst___redArg(v_a_3183_);
                    v_a_3214_ = leanh::lean_ctor_get(v___x_3213_, 0);
                    leanh::lean_inc(v_a_3214_);
                    leanh::lean_dec_ref(v___x_3213_);
                    v_val_3215_ = leanh::lean_ctor_get(v_a_3214_, 0);
                    leanh::lean_inc(v_val_3215_);
                    leanh::lean_dec(v_a_3214_);
                    v___x_3216_ = leanh::lean_box(0);
                    leanh::lean_inc(v_u_3193_);
                    v___x_3217_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3217_, 0, v_u_3193_);
                    leanh::lean_ctor_set(v___x_3217_, 1, v___x_3216_);
                    v___x_3218_ = l_Lean_mkConst(v___x_3196_, v___x_3217_);
                    leanh::lean_inc_ref(v_type_3194_);
                    v___x_3219_ =
                        l_Lean_mkApp3(v___x_3218_, v_type_3194_, v_val_3215_, v___x_3195_);
                    v_r_3190_ = v___x_3219_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_3195_);
                    if v_isShared_3210_ == 0 {
                        v___x_3221_ = v___x_3209_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3222_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3207_);
                        v___x_3221_ = v_reuseFailAlloc_3222_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3221_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___boxed(
    mut v_n_3226_: *mut leanh::LeanObject,
    mut v_a_3227_: *mut leanh::LeanObject,
    mut v_a_3228_: *mut leanh::LeanObject,
    mut v_a_3229_: *mut leanh::LeanObject,
    mut v_a_3230_: *mut leanh::LeanObject,
    mut v_a_3231_: *mut leanh::LeanObject,
    mut v_a_3232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3233_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_n_3226_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
    leanh::lean_dec(v_a_3231_);
    leanh::lean_dec_ref(v_a_3230_);
    leanh::lean_dec(v_a_3229_);
    leanh::lean_dec_ref(v_a_3228_);
    leanh::lean_dec_ref(v_a_3227_);
    leanh::lean_dec(v_n_3226_);
    return v_res_3233_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin_spec__0(
    mut v_a_3234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3235_ = lean_nat_to_int(v_a_3234_);
    return v___x_3235_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3241_ = leanh::lean_unsigned_to_nat(0);
    v___x_3242_ = l_Lean_Level_ofNat(v___x_3241_);
    return v___x_3242_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_3243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3243_ = leanh::lean_box(0);
    v___x_3244_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
    v___x_3245_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3245_, 0, v___x_3244_);
    leanh::lean_ctor_set(v___x_3245_, 1, v___x_3243_);
    return v___x_3245_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_3246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3246_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
    v___x_3247_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
    v___x_3248_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3248_, 0, v___x_3247_);
    leanh::lean_ctor_set(v___x_3248_, 1, v___x_3246_);
    return v___x_3248_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_3249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3249_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__5);
    v___x_3250_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__3);
    v___x_3251_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3251_, 0, v___x_3250_);
    leanh::lean_ctor_set(v___x_3251_, 1, v___x_3249_);
    return v___x_3251_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3252_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__6);
    v___x_3253_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2;
    v___x_3254_ = l_Lean_Expr_const___override(v___x_3253_, v___x_3252_);
    return v___x_3254_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3258_ = leanh::lean_box(0);
    v___x_3259_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__9;
    v___x_3260_ = l_Lean_Expr_const___override(v___x_3259_, v___x_3258_);
    return v___x_3260_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3261_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
    v___x_3262_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst___closed__1;
    v___x_3263_ = l_Lean_Expr_const___override(v___x_3262_, v___x_3261_);
    return v___x_3263_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3268_ = leanh::lean_box(0);
    v___x_3269_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__13;
    v___x_3270_ = l_Lean_Expr_const___override(v___x_3269_, v___x_3268_);
    return v___x_3270_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_3271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3271_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__14);
    v___x_3272_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
    v___x_3273_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__11);
    v___x_3274_ = l_Lean_mkAppB(v___x_3273_, v___x_3272_, v___x_3271_);
    return v___x_3274_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(
    mut v_declName_3275_: *mut leanh::LeanObject,
    mut v_a_3276_: *mut leanh::LeanObject,
    mut v_b_3277_: *mut leanh::LeanObject,
    mut v_r_u2081_3278_: *mut leanh::LeanObject,
    mut v_r_u2082_3279_: *mut leanh::LeanObject,
    mut v_op_3280_: *mut leanh::LeanObject,
    mut v_a_3281_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v_fst_3288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3292_: u8 = 0;
    let mut v_u_3293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_3295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isChar0Inst_3296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: u8 = 0;
    let mut v___x_3337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3356_: u8 = 0;
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3283_ = leanh::lean_ctor_get(v_r_u2081_3278_, 0);
                v_snd_3284_ = leanh::lean_ctor_get(v_r_u2081_3278_, 1);
                v_isSharedCheck_3357_ = (!leanh::lean_is_exclusive(v_r_u2081_3278_)) as u8;
                if v_isSharedCheck_3357_ == 0 {
                    v___x_3286_ = v_r_u2081_3278_;
                    v_isShared_3287_ = v_isSharedCheck_3357_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3284_);
                    leanh::lean_inc(v_fst_3283_);
                    leanh::lean_dec(v_r_u2081_3278_);
                    v___x_3286_ = leanh::lean_box(0);
                    v_isShared_3287_ = v_isSharedCheck_3357_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_3288_ = leanh::lean_ctor_get(v_r_u2082_3279_, 0);
                v_snd_3289_ = leanh::lean_ctor_get(v_r_u2082_3279_, 1);
                v_isSharedCheck_3356_ = (!leanh::lean_is_exclusive(v_r_u2082_3279_)) as u8;
                if v_isSharedCheck_3356_ == 0 {
                    v___x_3291_ = v_r_u2082_3279_;
                    v_isShared_3292_ = v_isSharedCheck_3356_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3289_);
                    leanh::lean_inc(v_fst_3288_);
                    leanh::lean_dec(v_r_u2082_3279_);
                    v___x_3291_ = leanh::lean_box(0);
                    v_isShared_3292_ = v_isSharedCheck_3356_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_u_3293_ = leanh::lean_ctor_get(v_a_3281_, 0);
                v_type_3294_ = leanh::lean_ctor_get(v_a_3281_, 1);
                v_fieldInst_3295_ = leanh::lean_ctor_get(v_a_3281_, 2);
                v_isChar0Inst_3296_ = leanh::lean_ctor_get(v_a_3281_, 3);
                v_num_3297_ = leanh::lean_ctor_get(v_fst_3283_, 0);
                leanh::lean_inc(v_num_3297_);
                v_den_3298_ = leanh::lean_ctor_get(v_fst_3283_, 1);
                leanh::lean_inc(v_den_3298_);
                leanh::lean_inc(v_fst_3288_);
                v___x_3299_ = leanh::lean_apply_2(v_op_3280_, v_fst_3283_, v_fst_3288_);
                v___x_3300_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_3293_);
                if v_isShared_3287_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_3286_, 1);
                    leanh::lean_ctor_set(v___x_3286_, 1, v___x_3300_);
                    leanh::lean_ctor_set(v___x_3286_, 0, v_u_3293_);
                    v___x_3302_ = v___x_3286_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3355_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_u_3293_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3355_, 1, v___x_3300_);
                    v___x_3302_ = v_reuseFailAlloc_3355_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3303_ = l_Lean_mkConst(v_declName_3275_, v___x_3302_);
                v___x_3345_ = leanh::lean_unsigned_to_nat(1);
                v___x_3346_ = lean_nat_dec_eq(v_den_3298_, v___x_3345_);
                if v___x_3346_ == 0 {
                    v___x_3347_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_3348_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_3349_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_3350_ = l_Lean_instToExprRat_mkInt(v_num_3297_);
                    leanh::lean_dec(v_num_3297_);
                    v___x_3351_ = lean_nat_to_int(v_den_3298_);
                    v___x_3352_ = l_Lean_instToExprRat_mkInt(v___x_3351_);
                    leanh::lean_dec(v___x_3351_);
                    v___x_3353_ = l_Lean_mkApp6(
                        v___x_3347_,
                        v___x_3348_,
                        v___x_3348_,
                        v___x_3348_,
                        v___x_3349_,
                        v___x_3350_,
                        v___x_3352_,
                    );
                    v___y_3332_ = v___x_3353_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_dec(v_den_3298_);
                    v___x_3354_ = l_Lean_instToExprRat_mkInt(v_num_3297_);
                    leanh::lean_dec(v_num_3297_);
                    v___y_3332_ = v___x_3354_;
                    state = 7;
                    continue;
                }
            }
            4 => {
                leanh::lean_inc_ref(v_isChar0Inst_3296_);
                leanh::lean_inc_ref(v_fieldInst_3295_);
                leanh::lean_inc_ref(v_type_3294_);
                v___x_3308_ = l_Lean_mkApp8(
                    v___x_3303_,
                    v_type_3294_,
                    v_fieldInst_3295_,
                    v_isChar0Inst_3296_,
                    v_a_3276_,
                    v_b_3277_,
                    v___y_3305_,
                    v___y_3306_,
                    v___y_3307_,
                );
                v___x_3309_ = l_Lean_eagerReflBoolTrue;
                v___x_3310_ = l_Lean_mkApp3(v___x_3308_, v___x_3309_, v_snd_3284_, v_snd_3289_);
                if v_isShared_3292_ == 0 {
                    leanh::lean_ctor_set(v___x_3291_, 1, v___x_3310_);
                    leanh::lean_ctor_set(v___x_3291_, 0, v___x_3299_);
                    v___x_3312_ = v___x_3291_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3315_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3315_, 0, v___x_3299_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3315_, 1, v___x_3310_);
                    v___x_3312_ = v_reuseFailAlloc_3315_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3313_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3313_, 0, v___x_3312_);
                v___x_3314_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3314_, 0, v___x_3313_);
                return v___x_3314_;
            }
            6 => {
                v_num_3319_ = leanh::lean_ctor_get(v___x_3299_, 0);
                leanh::lean_inc(v_num_3319_);
                v_den_3320_ = leanh::lean_ctor_get(v___x_3299_, 1);
                leanh::lean_inc(v_den_3320_);
                v___x_3321_ = leanh::lean_unsigned_to_nat(1);
                v___x_3322_ = lean_nat_dec_eq(v_den_3320_, v___x_3321_);
                if v___x_3322_ == 0 {
                    v___x_3323_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_3324_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_3325_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_3326_ = l_Lean_instToExprRat_mkInt(v_num_3319_);
                    leanh::lean_dec(v_num_3319_);
                    v___x_3327_ = lean_nat_to_int(v_den_3320_);
                    v___x_3328_ = l_Lean_instToExprRat_mkInt(v___x_3327_);
                    leanh::lean_dec(v___x_3327_);
                    v___x_3329_ = l_Lean_mkApp6(
                        v___x_3323_,
                        v___x_3324_,
                        v___x_3324_,
                        v___x_3324_,
                        v___x_3325_,
                        v___x_3326_,
                        v___x_3328_,
                    );
                    v___y_3305_ = v___y_3317_;
                    v___y_3306_ = v___y_3318_;
                    v___y_3307_ = v___x_3329_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_den_3320_);
                    v___x_3330_ = l_Lean_instToExprRat_mkInt(v_num_3319_);
                    leanh::lean_dec(v_num_3319_);
                    v___y_3305_ = v___y_3317_;
                    v___y_3306_ = v___y_3318_;
                    v___y_3307_ = v___x_3330_;
                    state = 4;
                    continue;
                }
            }
            7 => {
                v_num_3333_ = leanh::lean_ctor_get(v_fst_3288_, 0);
                leanh::lean_inc(v_num_3333_);
                v_den_3334_ = leanh::lean_ctor_get(v_fst_3288_, 1);
                leanh::lean_inc(v_den_3334_);
                leanh::lean_dec(v_fst_3288_);
                v___x_3335_ = leanh::lean_unsigned_to_nat(1);
                v___x_3336_ = lean_nat_dec_eq(v_den_3334_, v___x_3335_);
                if v___x_3336_ == 0 {
                    v___x_3337_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_3338_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_3339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_3340_ = l_Lean_instToExprRat_mkInt(v_num_3333_);
                    leanh::lean_dec(v_num_3333_);
                    v___x_3341_ = lean_nat_to_int(v_den_3334_);
                    v___x_3342_ = l_Lean_instToExprRat_mkInt(v___x_3341_);
                    leanh::lean_dec(v___x_3341_);
                    v___x_3343_ = l_Lean_mkApp6(
                        v___x_3337_,
                        v___x_3338_,
                        v___x_3338_,
                        v___x_3338_,
                        v___x_3339_,
                        v___x_3340_,
                        v___x_3342_,
                    );
                    v___y_3317_ = v___y_3332_;
                    v___y_3318_ = v___x_3343_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_den_3334_);
                    v___x_3344_ = l_Lean_instToExprRat_mkInt(v_num_3333_);
                    leanh::lean_dec(v_num_3333_);
                    v___y_3317_ = v___y_3332_;
                    v___y_3318_ = v___x_3344_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___boxed(
    mut v_declName_3358_: *mut leanh::LeanObject,
    mut v_a_3359_: *mut leanh::LeanObject,
    mut v_b_3360_: *mut leanh::LeanObject,
    mut v_r_u2081_3361_: *mut leanh::LeanObject,
    mut v_r_u2082_3362_: *mut leanh::LeanObject,
    mut v_op_3363_: *mut leanh::LeanObject,
    mut v_a_3364_: *mut leanh::LeanObject,
    mut v_a_3365_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3366_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_3358_, v_a_3359_, v_b_3360_, v_r_u2081_3361_, v_r_u2082_3362_, v_op_3363_, v_a_3364_);
    leanh::lean_dec_ref(v_a_3364_);
    return v_res_3366_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(
    mut v_declName_3367_: *mut leanh::LeanObject,
    mut v_a_3368_: *mut leanh::LeanObject,
    mut v_b_3369_: *mut leanh::LeanObject,
    mut v_r_u2081_3370_: *mut leanh::LeanObject,
    mut v_r_u2082_3371_: *mut leanh::LeanObject,
    mut v_op_3372_: *mut leanh::LeanObject,
    mut v_a_3373_: *mut leanh::LeanObject,
    mut v_a_3374_: *mut leanh::LeanObject,
    mut v_a_3375_: *mut leanh::LeanObject,
    mut v_a_3376_: *mut leanh::LeanObject,
    mut v_a_3377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3379_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v_declName_3367_, v_a_3368_, v_b_3369_, v_r_u2081_3370_, v_r_u2082_3371_, v_op_3372_, v_a_3373_);
    return v___x_3379_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___boxed(
    mut v_declName_3380_: *mut leanh::LeanObject,
    mut v_a_3381_: *mut leanh::LeanObject,
    mut v_b_3382_: *mut leanh::LeanObject,
    mut v_r_u2081_3383_: *mut leanh::LeanObject,
    mut v_r_u2082_3384_: *mut leanh::LeanObject,
    mut v_op_3385_: *mut leanh::LeanObject,
    mut v_a_3386_: *mut leanh::LeanObject,
    mut v_a_3387_: *mut leanh::LeanObject,
    mut v_a_3388_: *mut leanh::LeanObject,
    mut v_a_3389_: *mut leanh::LeanObject,
    mut v_a_3390_: *mut leanh::LeanObject,
    mut v_a_3391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3392_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin(v_declName_3380_, v_a_3381_, v_b_3382_, v_r_u2081_3383_, v_r_u2082_3384_, v_op_3385_, v_a_3386_, v_a_3387_, v_a_3388_, v_a_3389_, v_a_3390_);
    leanh::lean_dec(v_a_3390_);
    leanh::lean_dec_ref(v_a_3389_);
    leanh::lean_dec(v_a_3388_);
    leanh::lean_dec_ref(v_a_3387_);
    leanh::lean_dec_ref(v_a_3386_);
    return v_res_3392_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(
    mut v_declName_3393_: *mut leanh::LeanObject,
    mut v_a_3394_: *mut leanh::LeanObject,
    mut v_r_3395_: *mut leanh::LeanObject,
    mut v_op_3396_: *mut leanh::LeanObject,
    mut v_a_3397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3403_: u8 = 0;
    let mut v_u_3404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_3406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: u8 = 0;
    let mut v___x_3429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: u8 = 0;
    let mut v___x_3439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3399_ = leanh::lean_ctor_get(v_r_3395_, 0);
                v_snd_3400_ = leanh::lean_ctor_get(v_r_3395_, 1);
                v_isSharedCheck_3447_ = (!leanh::lean_is_exclusive(v_r_3395_)) as u8;
                if v_isSharedCheck_3447_ == 0 {
                    v___x_3402_ = v_r_3395_;
                    v_isShared_3403_ = v_isSharedCheck_3447_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_3400_);
                    leanh::lean_inc(v_fst_3399_);
                    leanh::lean_dec(v_r_3395_);
                    v___x_3402_ = leanh::lean_box(0);
                    v_isShared_3403_ = v_isSharedCheck_3447_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_u_3404_ = leanh::lean_ctor_get(v_a_3397_, 0);
                v_type_3405_ = leanh::lean_ctor_get(v_a_3397_, 1);
                v_fieldInst_3406_ = leanh::lean_ctor_get(v_a_3397_, 2);
                v_num_3407_ = leanh::lean_ctor_get(v_fst_3399_, 0);
                leanh::lean_inc(v_num_3407_);
                v_den_3408_ = leanh::lean_ctor_get(v_fst_3399_, 1);
                leanh::lean_inc(v_den_3408_);
                v___x_3409_ = leanh::lean_apply_1(v_op_3396_, v_fst_3399_);
                v___x_3410_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_3404_);
                v___x_3411_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_3411_, 0, v_u_3404_);
                leanh::lean_ctor_set(v___x_3411_, 1, v___x_3410_);
                v___x_3412_ = l_Lean_mkConst(v_declName_3393_, v___x_3411_);
                v___x_3437_ = leanh::lean_unsigned_to_nat(1);
                v___x_3438_ = lean_nat_dec_eq(v_den_3408_, v___x_3437_);
                if v___x_3438_ == 0 {
                    v___x_3439_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_3440_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_3441_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_3442_ = l_Lean_instToExprRat_mkInt(v_num_3407_);
                    leanh::lean_dec(v_num_3407_);
                    v___x_3443_ = lean_nat_to_int(v_den_3408_);
                    v___x_3444_ = l_Lean_instToExprRat_mkInt(v___x_3443_);
                    leanh::lean_dec(v___x_3443_);
                    v___x_3445_ = l_Lean_mkApp6(
                        v___x_3439_,
                        v___x_3440_,
                        v___x_3440_,
                        v___x_3440_,
                        v___x_3441_,
                        v___x_3442_,
                        v___x_3444_,
                    );
                    v___y_3424_ = v___x_3445_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec(v_den_3408_);
                    v___x_3446_ = l_Lean_instToExprRat_mkInt(v_num_3407_);
                    leanh::lean_dec(v_num_3407_);
                    v___y_3424_ = v___x_3446_;
                    state = 4;
                    continue;
                }
            }
            2 => {
                v___x_3416_ = l_Lean_eagerReflBoolTrue;
                leanh::lean_inc_ref(v_fieldInst_3406_);
                leanh::lean_inc_ref(v_type_3405_);
                v___x_3417_ = l_Lean_mkApp7(
                    v___x_3412_,
                    v_type_3405_,
                    v_fieldInst_3406_,
                    v_a_3394_,
                    v___y_3414_,
                    v___y_3415_,
                    v___x_3416_,
                    v_snd_3400_,
                );
                if v_isShared_3403_ == 0 {
                    leanh::lean_ctor_set(v___x_3402_, 1, v___x_3417_);
                    leanh::lean_ctor_set(v___x_3402_, 0, v___x_3409_);
                    v___x_3419_ = v___x_3402_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3422_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 0, v___x_3409_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3422_, 1, v___x_3417_);
                    v___x_3419_ = v_reuseFailAlloc_3422_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3420_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3420_, 0, v___x_3419_);
                v___x_3421_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_3421_, 0, v___x_3420_);
                return v___x_3421_;
            }
            4 => {
                v_num_3425_ = leanh::lean_ctor_get(v___x_3409_, 0);
                leanh::lean_inc(v_num_3425_);
                v_den_3426_ = leanh::lean_ctor_get(v___x_3409_, 1);
                leanh::lean_inc(v_den_3426_);
                v___x_3427_ = leanh::lean_unsigned_to_nat(1);
                v___x_3428_ = lean_nat_dec_eq(v_den_3426_, v___x_3427_);
                if v___x_3428_ == 0 {
                    v___x_3429_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_3430_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_3431_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_3432_ = l_Lean_instToExprRat_mkInt(v_num_3425_);
                    leanh::lean_dec(v_num_3425_);
                    v___x_3433_ = lean_nat_to_int(v_den_3426_);
                    v___x_3434_ = l_Lean_instToExprRat_mkInt(v___x_3433_);
                    leanh::lean_dec(v___x_3433_);
                    v___x_3435_ = l_Lean_mkApp6(
                        v___x_3429_,
                        v___x_3430_,
                        v___x_3430_,
                        v___x_3430_,
                        v___x_3431_,
                        v___x_3432_,
                        v___x_3434_,
                    );
                    v___y_3414_ = v___y_3424_;
                    v___y_3415_ = v___x_3435_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_den_3426_);
                    v___x_3436_ = l_Lean_instToExprRat_mkInt(v_num_3425_);
                    leanh::lean_dec(v_num_3425_);
                    v___y_3414_ = v___y_3424_;
                    v___y_3415_ = v___x_3436_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg___boxed(
    mut v_declName_3448_: *mut leanh::LeanObject,
    mut v_a_3449_: *mut leanh::LeanObject,
    mut v_r_3450_: *mut leanh::LeanObject,
    mut v_op_3451_: *mut leanh::LeanObject,
    mut v_a_3452_: *mut leanh::LeanObject,
    mut v_a_3453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3454_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_3448_, v_a_3449_, v_r_3450_, v_op_3451_, v_a_3452_);
    leanh::lean_dec_ref(v_a_3452_);
    return v_res_3454_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(
    mut v_declName_3455_: *mut leanh::LeanObject,
    mut v_a_3456_: *mut leanh::LeanObject,
    mut v_r_3457_: *mut leanh::LeanObject,
    mut v_op_3458_: *mut leanh::LeanObject,
    mut v_a_3459_: *mut leanh::LeanObject,
    mut v_a_3460_: *mut leanh::LeanObject,
    mut v_a_3461_: *mut leanh::LeanObject,
    mut v_a_3462_: *mut leanh::LeanObject,
    mut v_a_3463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3465_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3465_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v_declName_3455_, v_a_3456_, v_r_3457_, v_op_3458_, v_a_3459_);
    return v___x_3465_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___boxed(
    mut v_declName_3466_: *mut leanh::LeanObject,
    mut v_a_3467_: *mut leanh::LeanObject,
    mut v_r_3468_: *mut leanh::LeanObject,
    mut v_op_3469_: *mut leanh::LeanObject,
    mut v_a_3470_: *mut leanh::LeanObject,
    mut v_a_3471_: *mut leanh::LeanObject,
    mut v_a_3472_: *mut leanh::LeanObject,
    mut v_a_3473_: *mut leanh::LeanObject,
    mut v_a_3474_: *mut leanh::LeanObject,
    mut v_a_3475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3476_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary(v_declName_3466_, v_a_3467_, v_r_3468_, v_op_3469_, v_a_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
    leanh::lean_dec(v_a_3474_);
    leanh::lean_dec_ref(v_a_3473_);
    leanh::lean_dec(v_a_3472_);
    leanh::lean_dec_ref(v_a_3471_);
    leanh::lean_dec_ref(v_a_3470_);
    return v_res_3476_;
}
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__1(
    mut v_a_3477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3478_ = l_Rat_ofInt(v_a_3477_);
    return v___x_3478_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(
    mut v_a_3479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3480_ = lean_nat_to_int(v_a_3479_);
    v___x_3481_ = l_Rat_ofInt(v___x_3480_);
    return v___x_3481_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35()
-> *mut leanh::LeanObject {
    let mut v___x_3556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3556_ = leanh::lean_unsigned_to_nat(0);
    v___x_3557_ = lean_nat_to_int(v___x_3556_);
    return v___x_3557_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_3558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3558_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__4);
    v___x_3559_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7;
    v___x_3560_ = l_Lean_Expr_const___override(v___x_3559_, v___x_3558_);
    return v___x_3560_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39()
-> *mut leanh::LeanObject {
    let mut v___x_3564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3564_ = leanh::lean_box(0);
    v___x_3565_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__38;
    v___x_3566_ = l_Lean_Expr_const___override(v___x_3565_, v___x_3564_);
    return v___x_3566_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42()
-> *mut leanh::LeanObject {
    let mut v___x_3571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3571_ = leanh::lean_box(0);
    v___x_3572_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__41;
    v___x_3573_ = l_Lean_Expr_const___override(v___x_3572_, v___x_3571_);
    return v___x_3573_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(
    mut v_e_3618_: *mut leanh::LeanObject,
    mut v_a_3619_: *mut leanh::LeanObject,
    mut v_a_3620_: *mut leanh::LeanObject,
    mut v_a_3621_: *mut leanh::LeanObject,
    mut v_a_3622_: *mut leanh::LeanObject,
    mut v_a_3623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3629_: u8 = 0;
    let mut v___x_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: u8 = 0;
    let mut v_arg_3637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: u8 = 0;
    let mut v_arg_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3642_: u8 = 0;
    let mut v_arg_3643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: u8 = 0;
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    let mut v___x_3649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: u8 = 0;
    let mut v___x_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: u8 = 0;
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: u8 = 0;
    let mut v___x_3655_: u8 = 0;
    let mut v___x_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: u8 = 0;
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: u8 = 0;
    let mut v___x_3660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: u8 = 0;
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3666_: u8 = 0;
    let mut v___x_3667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: u8 = 0;
    let mut v___x_3669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: u8 = 0;
    let mut v___x_3671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3675_: u8 = 0;
    let mut v___x_3676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3681_: u8 = 0;
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3695_: u8 = 0;
    let mut v_a_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3699_: u8 = 0;
    let mut v___x_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3703_: u8 = 0;
    let mut v___x_3704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3708_: u8 = 0;
    let mut v___x_3709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3714_: u8 = 0;
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_a_3729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut v___x_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3741_: u8 = 0;
    let mut v___x_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3747_: u8 = 0;
    let mut v___x_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3761_: u8 = 0;
    let mut v_a_3762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3769_: u8 = 0;
    let mut v___x_3770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3774_: u8 = 0;
    let mut v___x_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: u8 = 0;
    let mut v___x_3781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3794_: u8 = 0;
    let mut v_a_3795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___x_3800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3802_: u8 = 0;
    let mut v___x_3803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3807_: u8 = 0;
    let mut v___x_3808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: u8 = 0;
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3818_: u8 = 0;
    let mut v___x_3819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3836_: u8 = 0;
    let mut v___x_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3841_: u8 = 0;
    let mut v_val_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3845_: u8 = 0;
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: u8 = 0;
    let mut v___x_3848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3852_: u8 = 0;
    let mut v___x_3853_: u8 = 0;
    let mut v___x_3854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isChar0Inst_3861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: u8 = 0;
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: u8 = 0;
    let mut v___x_3903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: u8 = 0;
    let mut v___x_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3922_: u8 = 0;
    let mut v_a_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3926_: u8 = 0;
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3930_: u8 = 0;
    let mut v_isSharedCheck_3931_: u8 = 0;
    let mut v___x_3932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3936_: u8 = 0;
    let mut v_a_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3940_: u8 = 0;
    let mut v___x_3942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3944_: u8 = 0;
    let mut v_isSharedCheck_3945_: u8 = 0;
    let mut v_isSharedCheck_3946_: u8 = 0;
    let mut v_a_3947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___x_3952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v___x_3955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3962_: u8 = 0;
    let mut v___x_3963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3967_: u8 = 0;
    let mut v_val_3968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3971_: u8 = 0;
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3976_: u8 = 0;
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_3984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isChar0Inst_3985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_3986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_3987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_num_4010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_4011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: u8 = 0;
    let mut v___x_4014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: u8 = 0;
    let mut v___x_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4032_: u8 = 0;
    let mut v_a_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4036_: u8 = 0;
    let mut v___x_4038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4040_: u8 = 0;
    let mut v_isSharedCheck_4041_: u8 = 0;
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4046_: u8 = 0;
    let mut v_a_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4050_: u8 = 0;
    let mut v___x_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4054_: u8 = 0;
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v_a_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v___x_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4069_: u8 = 0;
    let mut v___x_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: u8 = 0;
    let mut v___x_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_a_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4090_: u8 = 0;
    let mut v___x_4092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4094_: u8 = 0;
    let mut v___x_4095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4099_: u8 = 0;
    let mut v___x_4100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: u8 = 0;
    let mut v___x_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4116_: u8 = 0;
    let mut v_a_4117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4120_: u8 = 0;
    let mut v___x_4122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4124_: u8 = 0;
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4129_: u8 = 0;
    let mut v___x_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: u8 = 0;
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v_val_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v_u_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_4151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4166_: u8 = 0;
    let mut v___x_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4171_: u8 = 0;
    let mut v_a_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4175_: u8 = 0;
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4179_: u8 = 0;
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut v_a_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v___x_4194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v_val_4209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4212_: u8 = 0;
    let mut v_u_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4230_: u8 = 0;
    let mut v___x_4231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4235_: u8 = 0;
    let mut v_a_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4239_: u8 = 0;
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4243_: u8 = 0;
    let mut v_isSharedCheck_4244_: u8 = 0;
    let mut v_a_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4248_: u8 = 0;
    let mut v___x_4250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4257_: u8 = 0;
    let mut v___x_4258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: u8 = 0;
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4272_: u8 = 0;
    let mut v_val_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4276_: u8 = 0;
    let mut v_u_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_4279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: u8 = 0;
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4306_: u8 = 0;
    let mut v___x_4307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4311_: u8 = 0;
    let mut v_a_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4319_: u8 = 0;
    let mut v_isSharedCheck_4320_: u8 = 0;
    let mut v_a_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4324_: u8 = 0;
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4328_: u8 = 0;
    let mut v_isSharedCheck_4329_: u8 = 0;
    let mut v_a_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3625_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3618_, v_a_3621_);
                if leanh::lean_obj_tag(v___x_3625_) == 0 {
                    v_a_3626_ = leanh::lean_ctor_get(v___x_3625_, 0);
                    v_isSharedCheck_4329_ = (!leanh::lean_is_exclusive(v___x_3625_)) as u8;
                    if v_isSharedCheck_4329_ == 0 {
                        v___x_3628_ = v___x_3625_;
                        v_isShared_3629_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3626_);
                        leanh::lean_dec(v___x_3625_);
                        v___x_3628_ = leanh::lean_box(0);
                        v_isShared_3629_ = v_isSharedCheck_4329_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4330_ = leanh::lean_ctor_get(v___x_3625_, 0);
                    v_isSharedCheck_4337_ = (!leanh::lean_is_exclusive(v___x_3625_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4332_ = v___x_3625_;
                        v_isShared_4333_ = v_isSharedCheck_4337_;
                        state = 111;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4330_);
                        leanh::lean_dec(v___x_3625_);
                        v___x_4332_ = leanh::lean_box(0);
                        v_isShared_4333_ = v_isSharedCheck_4337_;
                        state = 111;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3635_ = l_Lean_Expr_cleanupAnnotations(v_a_3626_);
                v___x_3636_ = l_Lean_Expr_isApp(v___x_3635_);
                if v___x_3636_ == 0 {
                    leanh::lean_dec_ref(v___x_3635_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3637_ = leanh::lean_ctor_get(v___x_3635_, 1);
                    leanh::lean_inc_ref(v_arg_3637_);
                    v___x_3638_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3635_);
                    v___x_3639_ = l_Lean_Expr_isApp(v___x_3638_);
                    if v___x_3639_ == 0 {
                        leanh::lean_dec_ref(v___x_3638_);
                        leanh::lean_dec_ref(v_arg_3637_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_3640_ = leanh::lean_ctor_get(v___x_3638_, 1);
                        leanh::lean_inc_ref(v_arg_3640_);
                        v___x_3641_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3638_);
                        v___x_3642_ = l_Lean_Expr_isApp(v___x_3641_);
                        if v___x_3642_ == 0 {
                            leanh::lean_dec_ref(v___x_3641_);
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_3643_ = leanh::lean_ctor_get(v___x_3641_, 1);
                            leanh::lean_inc_ref(v_arg_3643_);
                            v___x_3644_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3641_);
                            v___x_3645_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1;
                            v___x_3646_ = l_Lean_Expr_isConstOf(v___x_3644_, v___x_3645_);
                            if v___x_3646_ == 0 {
                                v___x_3647_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1;
                                v___x_3648_ = l_Lean_Expr_isConstOf(v___x_3644_, v___x_3647_);
                                if v___x_3648_ == 0 {
                                    v___x_3649_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1;
                                    v___x_3650_ = l_Lean_Expr_isConstOf(v___x_3644_, v___x_3649_);
                                    if v___x_3650_ == 0 {
                                        v___x_3651_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4;
                                        v___x_3652_ =
                                            l_Lean_Expr_isConstOf(v___x_3644_, v___x_3651_);
                                        if v___x_3652_ == 0 {
                                            v___x_3653_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7;
                                            v___x_3654_ =
                                                l_Lean_Expr_isConstOf(v___x_3644_, v___x_3653_);
                                            if v___x_3654_ == 0 {
                                                v___x_3655_ = l_Lean_Expr_isApp(v___x_3644_);
                                                if v___x_3655_ == 0 {
                                                    leanh::lean_dec_ref(v___x_3644_);
                                                    leanh::lean_dec_ref(v_arg_3643_);
                                                    leanh::lean_dec_ref(v_arg_3640_);
                                                    leanh::lean_dec_ref(v_arg_3637_);
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_3656_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_3644_,
                                                    );
                                                    v___x_3657_ = l_Lean_Expr_isApp(v___x_3656_);
                                                    if v___x_3657_ == 0 {
                                                        leanh::lean_dec_ref(v___x_3656_);
                                                        leanh::lean_dec_ref(v_arg_3643_);
                                                        leanh::lean_dec_ref(v_arg_3640_);
                                                        leanh::lean_dec_ref(v_arg_3637_);
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v___x_3658_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_3656_,
                                                            );
                                                        v___x_3659_ =
                                                            l_Lean_Expr_isApp(v___x_3658_);
                                                        if v___x_3659_ == 0 {
                                                            leanh::lean_dec_ref(v___x_3658_);
                                                            leanh::lean_dec_ref(v_arg_3643_);
                                                            leanh::lean_dec_ref(v_arg_3640_);
                                                            leanh::lean_dec_ref(v_arg_3637_);
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            v___x_3660_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_3658_,
                                                                );
                                                            v___x_3661_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10;
                                                            v___x_3662_ = l_Lean_Expr_isConstOf(
                                                                v___x_3660_,
                                                                v___x_3661_,
                                                            );
                                                            if v___x_3662_ == 0 {
                                                                v___x_3663_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2;
                                                                v___x_3664_ = l_Lean_Expr_isConstOf(
                                                                    v___x_3660_,
                                                                    v___x_3663_,
                                                                );
                                                                if v___x_3664_ == 0 {
                                                                    v___x_3665_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13;
                                                                    v___x_3666_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_3660_,
                                                                            v___x_3665_,
                                                                        );
                                                                    if v___x_3666_ == 0 {
                                                                        v___x_3667_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16;
                                                                        v___x_3668_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_3660_,
                                                                                v___x_3667_,
                                                                            );
                                                                        if v___x_3668_ == 0 {
                                                                            v___x_3669_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19;
                                                                            v___x_3670_ = l_Lean_Expr_isConstOf(v___x_3660_, v___x_3669_);
                                                                            leanh::lean_dec_ref(v___x_3660_);
                                                                            if v___x_3670_ == 0 {
                                                                                leanh::lean_dec_ref(v_arg_3643_);
                                                                                leanh::lean_dec_ref(v_arg_3640_);
                                                                                leanh::lean_dec_ref(v_arg_3637_);
                                                                                state = 2;
                                                                                continue;
                                                                            } else {
                                                                                leanh::lean_del_object(v___x_3628_);
                                                                                v___x_3671_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isAddInst(v_arg_3643_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                                                                if leanh::lean_obj_tag(v___x_3671_) == 0 {
v_a_3672_ = leanh::lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3695_ = (!leanh::lean_is_exclusive(v___x_3671_)) as u8;
if v_isSharedCheck_3695_ == 0 {
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3695_;
state = 4; continue;
} else {
leanh::lean_inc(v_a_3672_);
leanh::lean_dec(v___x_3671_);
v___x_3674_ = leanh::lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3695_;
state = 4; continue;
}
} else {
leanh::lean_dec_ref(v_arg_3640_);
leanh::lean_dec_ref(v_arg_3637_);
v_a_3696_ = leanh::lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3703_ = (!leanh::lean_is_exclusive(v___x_3671_)) as u8;
if v_isSharedCheck_3703_ == 0 {
v___x_3698_ = v___x_3671_;
v_isShared_3699_ = v_isSharedCheck_3703_;
state = 7; continue;
} else {
leanh::lean_inc(v_a_3696_);
leanh::lean_dec(v___x_3671_);
v___x_3698_ = leanh::lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
state = 7; continue;
}
}
                                                                            }
                                                                        } else {
                                                                            leanh::lean_dec_ref(v___x_3660_);
                                                                            leanh::lean_del_object(v___x_3628_);
                                                                            v___x_3704_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isMulInst(v_arg_3643_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                                                            if leanh::lean_obj_tag(v___x_3704_) == 0 {
v_a_3705_ = leanh::lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3728_ = (!leanh::lean_is_exclusive(v___x_3704_)) as u8;
if v_isSharedCheck_3728_ == 0 {
v___x_3707_ = v___x_3704_;
v_isShared_3708_ = v_isSharedCheck_3728_;
state = 9; continue;
} else {
leanh::lean_inc(v_a_3705_);
leanh::lean_dec(v___x_3704_);
v___x_3707_ = leanh::lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3728_;
state = 9; continue;
}
} else {
leanh::lean_dec_ref(v_arg_3640_);
leanh::lean_dec_ref(v_arg_3637_);
v_a_3729_ = leanh::lean_ctor_get(v___x_3704_, 0);
v_isSharedCheck_3736_ = (!leanh::lean_is_exclusive(v___x_3704_)) as u8;
if v_isSharedCheck_3736_ == 0 {
v___x_3731_ = v___x_3704_;
v_isShared_3732_ = v_isSharedCheck_3736_;
state = 12; continue;
} else {
leanh::lean_inc(v_a_3729_);
leanh::lean_dec(v___x_3704_);
v___x_3731_ = leanh::lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
state = 12; continue;
}
}
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_3660_,
                                                                        );
                                                                        leanh::lean_del_object(v___x_3628_);
                                                                        v___x_3737_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isSubInst(v_arg_3643_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                                                        if leanh::lean_obj_tag(v___x_3737_) == 0 {
v_a_3738_ = leanh::lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3761_ = (!leanh::lean_is_exclusive(v___x_3737_)) as u8;
if v_isSharedCheck_3761_ == 0 {
v___x_3740_ = v___x_3737_;
v_isShared_3741_ = v_isSharedCheck_3761_;
state = 14; continue;
} else {
leanh::lean_inc(v_a_3738_);
leanh::lean_dec(v___x_3737_);
v___x_3740_ = leanh::lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3761_;
state = 14; continue;
}
} else {
leanh::lean_dec_ref(v_arg_3640_);
leanh::lean_dec_ref(v_arg_3637_);
v_a_3762_ = leanh::lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3769_ = (!leanh::lean_is_exclusive(v___x_3737_)) as u8;
if v_isSharedCheck_3769_ == 0 {
v___x_3764_ = v___x_3737_;
v_isShared_3765_ = v_isSharedCheck_3769_;
state = 17; continue;
} else {
leanh::lean_inc(v_a_3762_);
leanh::lean_dec(v___x_3737_);
v___x_3764_ = leanh::lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3769_;
state = 17; continue;
}
}
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_3660_,
                                                                    );
                                                                    leanh::lean_del_object(
                                                                        v___x_3628_,
                                                                    );
                                                                    v___x_3770_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isDivInst(v_arg_3643_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                                                    if leanh::lean_obj_tag(
                                                                        v___x_3770_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_3771_ = leanh::lean_ctor_get(v___x_3770_, 0);
                                                                        v_isSharedCheck_3794_ = (!leanh::lean_is_exclusive(v___x_3770_)) as u8;
                                                                        if v_isSharedCheck_3794_
                                                                            == 0
                                                                        {
                                                                            v___x_3773_ =
                                                                                v___x_3770_;
                                                                            v_isShared_3774_ = v_isSharedCheck_3794_;
                                                                            state = 19;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_3771_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3770_,
                                                                            );
                                                                            v___x_3773_ = leanh::lean_box(0);
                                                                            v_isShared_3774_ = v_isSharedCheck_3794_;
                                                                            state = 19;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_3640_,
                                                                        );
                                                                        leanh::lean_dec_ref(
                                                                            v_arg_3637_,
                                                                        );
                                                                        v_a_3795_ = leanh::lean_ctor_get(v___x_3770_, 0);
                                                                        v_isSharedCheck_3802_ = (!leanh::lean_is_exclusive(v___x_3770_)) as u8;
                                                                        if v_isSharedCheck_3802_
                                                                            == 0
                                                                        {
                                                                            v___x_3797_ =
                                                                                v___x_3770_;
                                                                            v_isShared_3798_ = v_isSharedCheck_3802_;
                                                                            state = 22;
                                                                            continue;
                                                                        } else {
                                                                            leanh::lean_inc(
                                                                                v_a_3795_,
                                                                            );
                                                                            leanh::lean_dec(
                                                                                v___x_3770_,
                                                                            );
                                                                            v___x_3797_ = leanh::lean_box(0);
                                                                            v_isShared_3798_ = v_isSharedCheck_3802_;
                                                                            state = 22;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_3660_,
                                                                );
                                                                leanh::lean_del_object(
                                                                    v___x_3628_,
                                                                );
                                                                leanh::lean_inc_ref(
                                                                    v_arg_3643_,
                                                                );
                                                                v___x_3803_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNPowInst(v_arg_3643_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                                                if leanh::lean_obj_tag(
                                                                    v___x_3803_,
                                                                ) == 0
                                                                {
                                                                    v_a_3804_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3803_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4056_ = (!leanh::lean_is_exclusive(v___x_3803_)) as u8;
                                                                    if v_isSharedCheck_4056_ == 0 {
                                                                        v___x_3806_ = v___x_3803_;
                                                                        v_isShared_3807_ =
                                                                            v_isSharedCheck_4056_;
                                                                        state = 24;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_3804_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3803_,
                                                                        );
                                                                        v___x_3806_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_3807_ =
                                                                            v_isSharedCheck_4056_;
                                                                        state = 24;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3643_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3640_,
                                                                    );
                                                                    leanh::lean_dec_ref(
                                                                        v_arg_3637_,
                                                                    );
                                                                    v_a_4057_ =
                                                                        leanh::lean_ctor_get(
                                                                            v___x_3803_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4064_ = (!leanh::lean_is_exclusive(v___x_3803_)) as u8;
                                                                    if v_isSharedCheck_4064_ == 0 {
                                                                        v___x_4059_ = v___x_3803_;
                                                                        v_isShared_4060_ =
                                                                            v_isSharedCheck_4064_;
                                                                        state = 62;
                                                                        continue;
                                                                    } else {
                                                                        leanh::lean_inc(
                                                                            v_a_4057_,
                                                                        );
                                                                        leanh::lean_dec(
                                                                            v___x_3803_,
                                                                        );
                                                                        v___x_4059_ =
                                                                            leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_4060_ =
                                                                            v_isSharedCheck_4064_;
                                                                        state = 62;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_3644_);
                                                leanh::lean_dec_ref(v_arg_3643_);
                                                leanh::lean_del_object(v___x_3628_);
                                                v___x_4065_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNegInst(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                                if leanh::lean_obj_tag(v___x_4065_) == 0 {
                                                    v_a_4066_ =
                                                        leanh::lean_ctor_get(v___x_4065_, 0);
                                                    v_isSharedCheck_4086_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4065_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4086_ == 0 {
                                                        v___x_4068_ = v___x_4065_;
                                                        v_isShared_4069_ = v_isSharedCheck_4086_;
                                                        state = 64;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4066_);
                                                        leanh::lean_dec(v___x_4065_);
                                                        v___x_4068_ = leanh::lean_box(0);
                                                        v_isShared_4069_ = v_isSharedCheck_4086_;
                                                        state = 64;
                                                        continue;
                                                    }
                                                } else {
                                                    leanh::lean_dec_ref(v_arg_3637_);
                                                    v_a_4087_ =
                                                        leanh::lean_ctor_get(v___x_4065_, 0);
                                                    v_isSharedCheck_4094_ =
                                                        (!leanh::lean_is_exclusive(
                                                            v___x_4065_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_4094_ == 0 {
                                                        v___x_4089_ = v___x_4065_;
                                                        v_isShared_4090_ = v_isSharedCheck_4094_;
                                                        state = 67;
                                                        continue;
                                                    } else {
                                                        leanh::lean_inc(v_a_4087_);
                                                        leanh::lean_dec(v___x_4065_);
                                                        v___x_4089_ = leanh::lean_box(0);
                                                        v_isShared_4090_ = v_isSharedCheck_4094_;
                                                        state = 67;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_3644_);
                                            leanh::lean_dec_ref(v_arg_3643_);
                                            leanh::lean_del_object(v___x_3628_);
                                            v___x_4095_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isInvInst(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                            if leanh::lean_obj_tag(v___x_4095_) == 0 {
                                                v_a_4096_ =
                                                    leanh::lean_ctor_get(v___x_4095_, 0);
                                                v_isSharedCheck_4116_ =
                                                    (!leanh::lean_is_exclusive(v___x_4095_))
                                                        as u8;
                                                if v_isSharedCheck_4116_ == 0 {
                                                    v___x_4098_ = v___x_4095_;
                                                    v_isShared_4099_ = v_isSharedCheck_4116_;
                                                    state = 69;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4096_);
                                                    leanh::lean_dec(v___x_4095_);
                                                    v___x_4098_ = leanh::lean_box(0);
                                                    v_isShared_4099_ = v_isSharedCheck_4116_;
                                                    state = 69;
                                                    continue;
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v_arg_3637_);
                                                v_a_4117_ =
                                                    leanh::lean_ctor_get(v___x_4095_, 0);
                                                v_isSharedCheck_4124_ =
                                                    (!leanh::lean_is_exclusive(v___x_4095_))
                                                        as u8;
                                                if v_isSharedCheck_4124_ == 0 {
                                                    v___x_4119_ = v___x_4095_;
                                                    v_isShared_4120_ = v_isSharedCheck_4124_;
                                                    state = 72;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_4117_);
                                                    leanh::lean_dec(v___x_4095_);
                                                    v___x_4119_ = leanh::lean_box(0);
                                                    v_isShared_4120_ = v_isSharedCheck_4124_;
                                                    state = 72;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_3644_);
                                        leanh::lean_dec_ref(v_arg_3643_);
                                        leanh::lean_del_object(v___x_3628_);
                                        leanh::lean_inc_ref(v_arg_3640_);
                                        v___x_4125_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isOfNatInst(v_arg_3637_, v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                        if leanh::lean_obj_tag(v___x_4125_) == 0 {
                                            v_a_4126_ = leanh::lean_ctor_get(v___x_4125_, 0);
                                            v_isSharedCheck_4180_ =
                                                (!leanh::lean_is_exclusive(v___x_4125_))
                                                    as u8;
                                            if v_isSharedCheck_4180_ == 0 {
                                                v___x_4128_ = v___x_4125_;
                                                v_isShared_4129_ = v_isSharedCheck_4180_;
                                                state = 74;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4126_);
                                                leanh::lean_dec(v___x_4125_);
                                                v___x_4128_ = leanh::lean_box(0);
                                                v_isShared_4129_ = v_isSharedCheck_4180_;
                                                state = 74;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v_arg_3640_);
                                            v_a_4181_ = leanh::lean_ctor_get(v___x_4125_, 0);
                                            v_isSharedCheck_4188_ =
                                                (!leanh::lean_is_exclusive(v___x_4125_))
                                                    as u8;
                                            if v_isSharedCheck_4188_ == 0 {
                                                v___x_4183_ = v___x_4125_;
                                                v_isShared_4184_ = v_isSharedCheck_4188_;
                                                state = 84;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_4181_);
                                                leanh::lean_dec(v___x_4125_);
                                                v___x_4183_ = leanh::lean_box(0);
                                                v_isShared_4184_ = v_isSharedCheck_4188_;
                                                state = 84;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_3644_);
                                    leanh::lean_dec_ref(v_arg_3643_);
                                    leanh::lean_del_object(v___x_3628_);
                                    v___x_4189_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isNatCastInst(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                    if leanh::lean_obj_tag(v___x_4189_) == 0 {
                                        v_a_4190_ = leanh::lean_ctor_get(v___x_4189_, 0);
                                        v_isSharedCheck_4244_ =
                                            (!leanh::lean_is_exclusive(v___x_4189_)) as u8;
                                        if v_isSharedCheck_4244_ == 0 {
                                            v___x_4192_ = v___x_4189_;
                                            v_isShared_4193_ = v_isSharedCheck_4244_;
                                            state = 86;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4190_);
                                            leanh::lean_dec(v___x_4189_);
                                            v___x_4192_ = leanh::lean_box(0);
                                            v_isShared_4193_ = v_isSharedCheck_4244_;
                                            state = 86;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v_arg_3637_);
                                        v_a_4245_ = leanh::lean_ctor_get(v___x_4189_, 0);
                                        v_isSharedCheck_4252_ =
                                            (!leanh::lean_is_exclusive(v___x_4189_)) as u8;
                                        if v_isSharedCheck_4252_ == 0 {
                                            v___x_4247_ = v___x_4189_;
                                            v_isShared_4248_ = v_isSharedCheck_4252_;
                                            state = 96;
                                            continue;
                                        } else {
                                            leanh::lean_inc(v_a_4245_);
                                            leanh::lean_dec(v___x_4189_);
                                            v___x_4247_ = leanh::lean_box(0);
                                            v_isShared_4248_ = v_isSharedCheck_4252_;
                                            state = 96;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_3644_);
                                leanh::lean_dec_ref(v_arg_3643_);
                                leanh::lean_del_object(v___x_3628_);
                                v___x_4253_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isIntCastInst(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                if leanh::lean_obj_tag(v___x_4253_) == 0 {
                                    v_a_4254_ = leanh::lean_ctor_get(v___x_4253_, 0);
                                    v_isSharedCheck_4320_ =
                                        (!leanh::lean_is_exclusive(v___x_4253_)) as u8;
                                    if v_isSharedCheck_4320_ == 0 {
                                        v___x_4256_ = v___x_4253_;
                                        v_isShared_4257_ = v_isSharedCheck_4320_;
                                        state = 98;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4254_);
                                        leanh::lean_dec(v___x_4253_);
                                        v___x_4256_ = leanh::lean_box(0);
                                        v_isShared_4257_ = v_isSharedCheck_4320_;
                                        state = 98;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_arg_3637_);
                                    v_a_4321_ = leanh::lean_ctor_get(v___x_4253_, 0);
                                    v_isSharedCheck_4328_ =
                                        (!leanh::lean_is_exclusive(v___x_4253_)) as u8;
                                    if v_isSharedCheck_4328_ == 0 {
                                        v___x_4323_ = v___x_4253_;
                                        v_isShared_4324_ = v_isSharedCheck_4328_;
                                        state = 109;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_4321_);
                                        leanh::lean_dec(v___x_4253_);
                                        v___x_4323_ = leanh::lean_box(0);
                                        v_isShared_4324_ = v_isSharedCheck_4328_;
                                        state = 109;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3631_ = leanh::lean_box(0);
                if v_isShared_3629_ == 0 {
                    leanh::lean_ctor_set(v___x_3628_, 0, v___x_3631_);
                    v___x_3633_ = v___x_3628_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3634_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3631_);
                    v___x_3633_ = v_reuseFailAlloc_3634_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3633_;
            }
            4 => {
                if leanh::lean_obj_tag(v_a_3672_) == 0 {
                    leanh::lean_dec_ref(v_arg_3640_);
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_3676_ = leanh::lean_box(0);
                    if v_isShared_3675_ == 0 {
                        leanh::lean_ctor_set(v___x_3674_, 0, v___x_3676_);
                        v___x_3678_ = v___x_3674_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3676_);
                        v___x_3678_ = v_reuseFailAlloc_3679_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_val_3680_ = leanh::lean_ctor_get(v_a_3672_, 0);
                    leanh::lean_inc(v_val_3680_);
                    leanh::lean_dec_ref_known(v_a_3672_, 1);
                    v___x_3681_ = (leanh::lean_unbox(v_val_3680_) as u8);
                    leanh::lean_dec(v_val_3680_);
                    if v___x_3681_ == 0 {
                        leanh::lean_dec_ref(v_arg_3640_);
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_3682_ = leanh::lean_box(0);
                        if v_isShared_3675_ == 0 {
                            leanh::lean_ctor_set(v___x_3674_, 0, v___x_3682_);
                            v___x_3684_ = v___x_3674_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_3685_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
                            v___x_3684_ = v_reuseFailAlloc_3685_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3674_);
                        leanh::lean_inc_ref(v_arg_3640_);
                        v___x_3686_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_3686_) == 0 {
                            v_a_3687_ = leanh::lean_ctor_get(v___x_3686_, 0);
                            leanh::lean_inc(v_a_3687_);
                            if leanh::lean_obj_tag(v_a_3687_) == 0 {
                                leanh::lean_dec_ref(v_arg_3640_);
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_3686_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_3686_, 1);
                                v_val_3688_ = leanh::lean_ctor_get(v_a_3687_, 0);
                                leanh::lean_inc(v_val_3688_);
                                leanh::lean_dec_ref_known(v_a_3687_, 1);
                                leanh::lean_inc_ref(v_arg_3637_);
                                v___x_3689_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3637_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                if leanh::lean_obj_tag(v___x_3689_) == 0 {
                                    v_a_3690_ = leanh::lean_ctor_get(v___x_3689_, 0);
                                    leanh::lean_inc(v_a_3690_);
                                    if leanh::lean_obj_tag(v_a_3690_) == 0 {
                                        leanh::lean_dec(v_val_3688_);
                                        leanh::lean_dec_ref(v_arg_3640_);
                                        leanh::lean_dec_ref(v_arg_3637_);
                                        return v___x_3689_;
                                    } else {
                                        leanh::lean_dec_ref_known(v___x_3689_, 1);
                                        v_val_3691_ = leanh::lean_ctor_get(v_a_3690_, 0);
                                        leanh::lean_inc(v_val_3691_);
                                        leanh::lean_dec_ref_known(v_a_3690_, 1);
                                        v___f_3692_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__20;
                                        v___x_3693_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__23;
                                        v___x_3694_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_3693_, v_arg_3640_, v_arg_3637_, v_val_3688_, v_val_3691_, v___f_3692_, v_a_3619_);
                                        return v___x_3694_;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_3688_);
                                    leanh::lean_dec_ref(v_arg_3640_);
                                    leanh::lean_dec_ref(v_arg_3637_);
                                    return v___x_3689_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_3686_;
                        }
                    }
                }
            }
            5 => {
                return v___x_3678_;
            }
            6 => {
                return v___x_3684_;
            }
            7 => {
                if v_isShared_3699_ == 0 {
                    v___x_3701_ = v___x_3698_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3702_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
                    v___x_3701_ = v_reuseFailAlloc_3702_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3701_;
            }
            9 => {
                if leanh::lean_obj_tag(v_a_3705_) == 0 {
                    leanh::lean_dec_ref(v_arg_3640_);
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_3709_ = leanh::lean_box(0);
                    if v_isShared_3708_ == 0 {
                        leanh::lean_ctor_set(v___x_3707_, 0, v___x_3709_);
                        v___x_3711_ = v___x_3707_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_3712_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3712_, 0, v___x_3709_);
                        v___x_3711_ = v_reuseFailAlloc_3712_;
                        state = 10;
                        continue;
                    }
                } else {
                    v_val_3713_ = leanh::lean_ctor_get(v_a_3705_, 0);
                    leanh::lean_inc(v_val_3713_);
                    leanh::lean_dec_ref_known(v_a_3705_, 1);
                    v___x_3714_ = (leanh::lean_unbox(v_val_3713_) as u8);
                    leanh::lean_dec(v_val_3713_);
                    if v___x_3714_ == 0 {
                        leanh::lean_dec_ref(v_arg_3640_);
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_3715_ = leanh::lean_box(0);
                        if v_isShared_3708_ == 0 {
                            leanh::lean_ctor_set(v___x_3707_, 0, v___x_3715_);
                            v___x_3717_ = v___x_3707_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3718_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3718_, 0, v___x_3715_);
                            v___x_3717_ = v_reuseFailAlloc_3718_;
                            state = 11;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3707_);
                        leanh::lean_inc_ref(v_arg_3640_);
                        v___x_3719_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_3719_) == 0 {
                            v_a_3720_ = leanh::lean_ctor_get(v___x_3719_, 0);
                            leanh::lean_inc(v_a_3720_);
                            if leanh::lean_obj_tag(v_a_3720_) == 0 {
                                leanh::lean_dec_ref(v_arg_3640_);
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_3719_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_3719_, 1);
                                v_val_3721_ = leanh::lean_ctor_get(v_a_3720_, 0);
                                leanh::lean_inc(v_val_3721_);
                                leanh::lean_dec_ref_known(v_a_3720_, 1);
                                leanh::lean_inc_ref(v_arg_3637_);
                                v___x_3722_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3637_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                if leanh::lean_obj_tag(v___x_3722_) == 0 {
                                    v_a_3723_ = leanh::lean_ctor_get(v___x_3722_, 0);
                                    leanh::lean_inc(v_a_3723_);
                                    if leanh::lean_obj_tag(v_a_3723_) == 0 {
                                        leanh::lean_dec(v_val_3721_);
                                        leanh::lean_dec_ref(v_arg_3640_);
                                        leanh::lean_dec_ref(v_arg_3637_);
                                        return v___x_3722_;
                                    } else {
                                        leanh::lean_dec_ref_known(v___x_3722_, 1);
                                        v_val_3724_ = leanh::lean_ctor_get(v_a_3723_, 0);
                                        leanh::lean_inc(v_val_3724_);
                                        leanh::lean_dec_ref_known(v_a_3723_, 1);
                                        v___f_3725_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__24;
                                        v___x_3726_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__26;
                                        v___x_3727_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_3726_, v_arg_3640_, v_arg_3637_, v_val_3721_, v_val_3724_, v___f_3725_, v_a_3619_);
                                        return v___x_3727_;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_3721_);
                                    leanh::lean_dec_ref(v_arg_3640_);
                                    leanh::lean_dec_ref(v_arg_3637_);
                                    return v___x_3722_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_3719_;
                        }
                    }
                }
            }
            10 => {
                return v___x_3711_;
            }
            11 => {
                return v___x_3717_;
            }
            12 => {
                if v_isShared_3732_ == 0 {
                    v___x_3734_ = v___x_3731_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
                    v___x_3734_ = v_reuseFailAlloc_3735_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3734_;
            }
            14 => {
                if leanh::lean_obj_tag(v_a_3738_) == 0 {
                    leanh::lean_dec_ref(v_arg_3640_);
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_3742_ = leanh::lean_box(0);
                    if v_isShared_3741_ == 0 {
                        leanh::lean_ctor_set(v___x_3740_, 0, v___x_3742_);
                        v___x_3744_ = v___x_3740_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3745_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3742_);
                        v___x_3744_ = v_reuseFailAlloc_3745_;
                        state = 15;
                        continue;
                    }
                } else {
                    v_val_3746_ = leanh::lean_ctor_get(v_a_3738_, 0);
                    leanh::lean_inc(v_val_3746_);
                    leanh::lean_dec_ref_known(v_a_3738_, 1);
                    v___x_3747_ = (leanh::lean_unbox(v_val_3746_) as u8);
                    leanh::lean_dec(v_val_3746_);
                    if v___x_3747_ == 0 {
                        leanh::lean_dec_ref(v_arg_3640_);
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_3748_ = leanh::lean_box(0);
                        if v_isShared_3741_ == 0 {
                            leanh::lean_ctor_set(v___x_3740_, 0, v___x_3748_);
                            v___x_3750_ = v___x_3740_;
                            state = 16;
                            continue;
                        } else {
                            v_reuseFailAlloc_3751_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3751_, 0, v___x_3748_);
                            v___x_3750_ = v_reuseFailAlloc_3751_;
                            state = 16;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3740_);
                        leanh::lean_inc_ref(v_arg_3640_);
                        v___x_3752_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_3752_) == 0 {
                            v_a_3753_ = leanh::lean_ctor_get(v___x_3752_, 0);
                            leanh::lean_inc(v_a_3753_);
                            if leanh::lean_obj_tag(v_a_3753_) == 0 {
                                leanh::lean_dec_ref(v_arg_3640_);
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_3752_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_3752_, 1);
                                v_val_3754_ = leanh::lean_ctor_get(v_a_3753_, 0);
                                leanh::lean_inc(v_val_3754_);
                                leanh::lean_dec_ref_known(v_a_3753_, 1);
                                leanh::lean_inc_ref(v_arg_3637_);
                                v___x_3755_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3637_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                if leanh::lean_obj_tag(v___x_3755_) == 0 {
                                    v_a_3756_ = leanh::lean_ctor_get(v___x_3755_, 0);
                                    leanh::lean_inc(v_a_3756_);
                                    if leanh::lean_obj_tag(v_a_3756_) == 0 {
                                        leanh::lean_dec(v_val_3754_);
                                        leanh::lean_dec_ref(v_arg_3640_);
                                        leanh::lean_dec_ref(v_arg_3637_);
                                        return v___x_3755_;
                                    } else {
                                        leanh::lean_dec_ref_known(v___x_3755_, 1);
                                        v_val_3757_ = leanh::lean_ctor_get(v_a_3756_, 0);
                                        leanh::lean_inc(v_val_3757_);
                                        leanh::lean_dec_ref_known(v_a_3756_, 1);
                                        v___f_3758_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__27;
                                        v___x_3759_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__29;
                                        v___x_3760_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_3759_, v_arg_3640_, v_arg_3637_, v_val_3754_, v_val_3757_, v___f_3758_, v_a_3619_);
                                        return v___x_3760_;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_3754_);
                                    leanh::lean_dec_ref(v_arg_3640_);
                                    leanh::lean_dec_ref(v_arg_3637_);
                                    return v___x_3755_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_3752_;
                        }
                    }
                }
            }
            15 => {
                return v___x_3744_;
            }
            16 => {
                return v___x_3750_;
            }
            17 => {
                if v_isShared_3765_ == 0 {
                    v___x_3767_ = v___x_3764_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3768_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_a_3762_);
                    v___x_3767_ = v_reuseFailAlloc_3768_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3767_;
            }
            19 => {
                if leanh::lean_obj_tag(v_a_3771_) == 0 {
                    leanh::lean_dec_ref(v_arg_3640_);
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_3775_ = leanh::lean_box(0);
                    if v_isShared_3774_ == 0 {
                        leanh::lean_ctor_set(v___x_3773_, 0, v___x_3775_);
                        v___x_3777_ = v___x_3773_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3778_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
                        v___x_3777_ = v_reuseFailAlloc_3778_;
                        state = 20;
                        continue;
                    }
                } else {
                    v_val_3779_ = leanh::lean_ctor_get(v_a_3771_, 0);
                    leanh::lean_inc(v_val_3779_);
                    leanh::lean_dec_ref_known(v_a_3771_, 1);
                    v___x_3780_ = (leanh::lean_unbox(v_val_3779_) as u8);
                    leanh::lean_dec(v_val_3779_);
                    if v___x_3780_ == 0 {
                        leanh::lean_dec_ref(v_arg_3640_);
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_3781_ = leanh::lean_box(0);
                        if v_isShared_3774_ == 0 {
                            leanh::lean_ctor_set(v___x_3773_, 0, v___x_3781_);
                            v___x_3783_ = v___x_3773_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_3784_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3781_);
                            v___x_3783_ = v_reuseFailAlloc_3784_;
                            state = 21;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3773_);
                        leanh::lean_inc_ref(v_arg_3640_);
                        v___x_3785_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_3785_) == 0 {
                            v_a_3786_ = leanh::lean_ctor_get(v___x_3785_, 0);
                            leanh::lean_inc(v_a_3786_);
                            if leanh::lean_obj_tag(v_a_3786_) == 0 {
                                leanh::lean_dec_ref(v_arg_3640_);
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_3785_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_3785_, 1);
                                v_val_3787_ = leanh::lean_ctor_get(v_a_3786_, 0);
                                leanh::lean_inc(v_val_3787_);
                                leanh::lean_dec_ref_known(v_a_3786_, 1);
                                leanh::lean_inc_ref(v_arg_3637_);
                                v___x_3788_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3637_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                                if leanh::lean_obj_tag(v___x_3788_) == 0 {
                                    v_a_3789_ = leanh::lean_ctor_get(v___x_3788_, 0);
                                    leanh::lean_inc(v_a_3789_);
                                    if leanh::lean_obj_tag(v_a_3789_) == 0 {
                                        leanh::lean_dec(v_val_3787_);
                                        leanh::lean_dec_ref(v_arg_3640_);
                                        leanh::lean_dec_ref(v_arg_3637_);
                                        return v___x_3788_;
                                    } else {
                                        leanh::lean_dec_ref_known(v___x_3788_, 1);
                                        v_val_3790_ = leanh::lean_ctor_get(v_a_3789_, 0);
                                        leanh::lean_inc(v_val_3790_);
                                        leanh::lean_dec_ref_known(v_a_3789_, 1);
                                        v___f_3791_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__30;
                                        v___x_3792_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__32;
                                        v___x_3793_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg(v___x_3792_, v_arg_3640_, v_arg_3637_, v_val_3787_, v_val_3790_, v___f_3791_, v_a_3619_);
                                        return v___x_3793_;
                                    }
                                } else {
                                    leanh::lean_dec(v_val_3787_);
                                    leanh::lean_dec_ref(v_arg_3640_);
                                    leanh::lean_dec_ref(v_arg_3637_);
                                    return v___x_3788_;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_3785_;
                        }
                    }
                }
            }
            20 => {
                return v___x_3777_;
            }
            21 => {
                return v___x_3783_;
            }
            22 => {
                if v_isShared_3798_ == 0 {
                    v___x_3800_ = v___x_3797_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3801_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3801_, 0, v_a_3795_);
                    v___x_3800_ = v_reuseFailAlloc_3801_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3800_;
            }
            24 => {
                if leanh::lean_obj_tag(v_a_3804_) == 0 {
                    leanh::lean_dec_ref(v_arg_3643_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_3808_ = leanh::lean_box(0);
                    if v_isShared_3807_ == 0 {
                        leanh::lean_ctor_set(v___x_3806_, 0, v___x_3808_);
                        v___x_3810_ = v___x_3806_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_3811_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
                        v___x_3810_ = v_reuseFailAlloc_3811_;
                        state = 25;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3806_);
                    v_val_3812_ = leanh::lean_ctor_get(v_a_3804_, 0);
                    leanh::lean_inc(v_val_3812_);
                    leanh::lean_dec_ref_known(v_a_3804_, 1);
                    v___x_3813_ = (leanh::lean_unbox(v_val_3812_) as u8);
                    if v___x_3813_ == 0 {
                        v___x_3814_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isZPowInst(v_arg_3643_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_3814_) == 0 {
                            v_a_3815_ = leanh::lean_ctor_get(v___x_3814_, 0);
                            v_isSharedCheck_3946_ =
                                (!leanh::lean_is_exclusive(v___x_3814_)) as u8;
                            if v_isSharedCheck_3946_ == 0 {
                                v___x_3817_ = v___x_3814_;
                                v_isShared_3818_ = v_isSharedCheck_3946_;
                                state = 26;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3815_);
                                leanh::lean_dec(v___x_3814_);
                                v___x_3817_ = leanh::lean_box(0);
                                v_isShared_3818_ = v_isSharedCheck_3946_;
                                state = 26;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_val_3812_);
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            v_a_3947_ = leanh::lean_ctor_get(v___x_3814_, 0);
                            v_isSharedCheck_3954_ =
                                (!leanh::lean_is_exclusive(v___x_3814_)) as u8;
                            if v_isSharedCheck_3954_ == 0 {
                                v___x_3949_ = v___x_3814_;
                                v_isShared_3950_ = v_isSharedCheck_3954_;
                                state = 45;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3947_);
                                leanh::lean_dec(v___x_3814_);
                                v___x_3949_ = leanh::lean_box(0);
                                v_isShared_3950_ = v_isSharedCheck_3954_;
                                state = 45;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_val_3812_);
                        leanh::lean_dec_ref(v_arg_3643_);
                        leanh::lean_inc_ref(v_arg_3640_);
                        v___x_3955_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_3955_) == 0 {
                            v_a_3956_ = leanh::lean_ctor_get(v___x_3955_, 0);
                            leanh::lean_inc(v_a_3956_);
                            if leanh::lean_obj_tag(v_a_3956_) == 0 {
                                leanh::lean_dec_ref(v_arg_3640_);
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_3955_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_3955_, 1);
                                v_val_3957_ = leanh::lean_ctor_get(v_a_3956_, 0);
                                leanh::lean_inc(v_val_3957_);
                                leanh::lean_dec_ref_known(v_a_3956_, 1);
                                v_fst_3958_ = leanh::lean_ctor_get(v_val_3957_, 0);
                                v_snd_3959_ = leanh::lean_ctor_get(v_val_3957_, 1);
                                v_isSharedCheck_4055_ =
                                    (!leanh::lean_is_exclusive(v_val_3957_)) as u8;
                                if v_isSharedCheck_4055_ == 0 {
                                    v___x_3961_ = v_val_3957_;
                                    v_isShared_3962_ = v_isSharedCheck_4055_;
                                    state = 47;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_snd_3959_);
                                    leanh::lean_inc(v_fst_3958_);
                                    leanh::lean_dec(v_val_3957_);
                                    v___x_3961_ = leanh::lean_box(0);
                                    v_isShared_3962_ = v_isSharedCheck_4055_;
                                    state = 47;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_3955_;
                        }
                    }
                }
            }
            25 => {
                return v___x_3810_;
            }
            26 => {
                if leanh::lean_obj_tag(v_a_3815_) == 0 {
                    leanh::lean_dec(v_val_3812_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_3819_ = leanh::lean_box(0);
                    if v_isShared_3818_ == 0 {
                        leanh::lean_ctor_set(v___x_3817_, 0, v___x_3819_);
                        v___x_3821_ = v___x_3817_;
                        state = 27;
                        continue;
                    } else {
                        v_reuseFailAlloc_3822_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3819_);
                        v___x_3821_ = v_reuseFailAlloc_3822_;
                        state = 27;
                        continue;
                    }
                } else {
                    v_val_3823_ = leanh::lean_ctor_get(v_a_3815_, 0);
                    leanh::lean_inc(v_val_3823_);
                    leanh::lean_dec_ref_known(v_a_3815_, 1);
                    v___x_3824_ = (leanh::lean_unbox(v_val_3823_) as u8);
                    leanh::lean_dec(v_val_3823_);
                    if v___x_3824_ == 0 {
                        leanh::lean_dec(v_val_3812_);
                        leanh::lean_dec_ref(v_arg_3640_);
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_3825_ = leanh::lean_box(0);
                        if v_isShared_3818_ == 0 {
                            leanh::lean_ctor_set(v___x_3817_, 0, v___x_3825_);
                            v___x_3827_ = v___x_3817_;
                            state = 28;
                            continue;
                        } else {
                            v_reuseFailAlloc_3828_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3825_);
                            v___x_3827_ = v_reuseFailAlloc_3828_;
                            state = 28;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_3817_);
                        leanh::lean_inc_ref(v_arg_3640_);
                        v___x_3829_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3640_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_3829_) == 0 {
                            v_a_3830_ = leanh::lean_ctor_get(v___x_3829_, 0);
                            leanh::lean_inc(v_a_3830_);
                            if leanh::lean_obj_tag(v_a_3830_) == 0 {
                                leanh::lean_dec(v_val_3812_);
                                leanh::lean_dec_ref(v_arg_3640_);
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_3829_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_3829_, 1);
                                v_val_3831_ = leanh::lean_ctor_get(v_a_3830_, 0);
                                leanh::lean_inc(v_val_3831_);
                                leanh::lean_dec_ref_known(v_a_3830_, 1);
                                v_fst_3832_ = leanh::lean_ctor_get(v_val_3831_, 0);
                                v_snd_3833_ = leanh::lean_ctor_get(v_val_3831_, 1);
                                v_isSharedCheck_3945_ =
                                    (!leanh::lean_is_exclusive(v_val_3831_)) as u8;
                                if v_isSharedCheck_3945_ == 0 {
                                    v___x_3835_ = v_val_3831_;
                                    v_isShared_3836_ = v_isSharedCheck_3945_;
                                    state = 29;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_snd_3833_);
                                    leanh::lean_inc(v_fst_3832_);
                                    leanh::lean_dec(v_val_3831_);
                                    v___x_3835_ = leanh::lean_box(0);
                                    v_isShared_3836_ = v_isSharedCheck_3945_;
                                    state = 29;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_val_3812_);
                            leanh::lean_dec_ref(v_arg_3640_);
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_3829_;
                        }
                    }
                }
            }
            27 => {
                return v___x_3821_;
            }
            28 => {
                return v___x_3827_;
            }
            29 => {
                v___x_3837_ = l_Lean_Meta_getIntValue_x3f(
                    v_arg_3637_,
                    v_a_3620_,
                    v_a_3621_,
                    v_a_3622_,
                    v_a_3623_,
                );
                if leanh::lean_obj_tag(v___x_3837_) == 0 {
                    v_a_3838_ = leanh::lean_ctor_get(v___x_3837_, 0);
                    v_isSharedCheck_3936_ = (!leanh::lean_is_exclusive(v___x_3837_)) as u8;
                    if v_isSharedCheck_3936_ == 0 {
                        v___x_3840_ = v___x_3837_;
                        v_isShared_3841_ = v_isSharedCheck_3936_;
                        state = 30;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3838_);
                        leanh::lean_dec(v___x_3837_);
                        v___x_3840_ = leanh::lean_box(0);
                        v_isShared_3841_ = v_isSharedCheck_3936_;
                        state = 30;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3835_);
                    leanh::lean_dec(v_snd_3833_);
                    leanh::lean_dec(v_fst_3832_);
                    leanh::lean_dec(v_val_3812_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v_a_3937_ = leanh::lean_ctor_get(v___x_3837_, 0);
                    v_isSharedCheck_3944_ = (!leanh::lean_is_exclusive(v___x_3837_)) as u8;
                    if v_isSharedCheck_3944_ == 0 {
                        v___x_3939_ = v___x_3837_;
                        v_isShared_3940_ = v_isSharedCheck_3944_;
                        state = 43;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3937_);
                        leanh::lean_dec(v___x_3837_);
                        v___x_3939_ = leanh::lean_box(0);
                        v_isShared_3940_ = v_isSharedCheck_3944_;
                        state = 43;
                        continue;
                    }
                }
            }
            30 => {
                if leanh::lean_obj_tag(v_a_3838_) == 1 {
                    leanh::lean_del_object(v___x_3840_);
                    v_val_3842_ = leanh::lean_ctor_get(v_a_3838_, 0);
                    v_isSharedCheck_3931_ = (!leanh::lean_is_exclusive(v_a_3838_)) as u8;
                    if v_isSharedCheck_3931_ == 0 {
                        v___x_3844_ = v_a_3838_;
                        v_isShared_3845_ = v_isSharedCheck_3931_;
                        state = 31;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3842_);
                        leanh::lean_dec(v_a_3838_);
                        v___x_3844_ = leanh::lean_box(0);
                        v_isShared_3845_ = v_isSharedCheck_3931_;
                        state = 31;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3838_);
                    leanh::lean_del_object(v___x_3835_);
                    leanh::lean_dec(v_snd_3833_);
                    leanh::lean_dec(v_fst_3832_);
                    leanh::lean_dec(v_val_3812_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v___x_3932_ = leanh::lean_box(0);
                    if v_isShared_3841_ == 0 {
                        leanh::lean_ctor_set(v___x_3840_, 0, v___x_3932_);
                        v___x_3934_ = v___x_3840_;
                        state = 42;
                        continue;
                    } else {
                        v_reuseFailAlloc_3935_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3935_, 0, v___x_3932_);
                        v___x_3934_ = v_reuseFailAlloc_3935_;
                        state = 42;
                        continue;
                    }
                }
            }
            31 => {
                v___x_3846_ = lean_nat_abs(v_val_3842_);
                v___x_3847_ = (leanh::lean_unbox(v_val_3812_) as u8);
                leanh::lean_dec(v_val_3812_);
                v___x_3848_ = l_Lean_checkExponent(v___x_3846_, v___x_3847_, v_a_3622_, v_a_3623_);
                if leanh::lean_obj_tag(v___x_3848_) == 0 {
                    v_a_3849_ = leanh::lean_ctor_get(v___x_3848_, 0);
                    v_isSharedCheck_3922_ = (!leanh::lean_is_exclusive(v___x_3848_)) as u8;
                    if v_isSharedCheck_3922_ == 0 {
                        v___x_3851_ = v___x_3848_;
                        v_isShared_3852_ = v_isSharedCheck_3922_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3849_);
                        leanh::lean_dec(v___x_3848_);
                        v___x_3851_ = leanh::lean_box(0);
                        v_isShared_3852_ = v_isSharedCheck_3922_;
                        state = 32;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3844_);
                    leanh::lean_dec(v_val_3842_);
                    leanh::lean_del_object(v___x_3835_);
                    leanh::lean_dec(v_snd_3833_);
                    leanh::lean_dec(v_fst_3832_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v_a_3923_ = leanh::lean_ctor_get(v___x_3848_, 0);
                    v_isSharedCheck_3930_ = (!leanh::lean_is_exclusive(v___x_3848_)) as u8;
                    if v_isSharedCheck_3930_ == 0 {
                        v___x_3925_ = v___x_3848_;
                        v_isShared_3926_ = v_isSharedCheck_3930_;
                        state = 40;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3923_);
                        leanh::lean_dec(v___x_3848_);
                        v___x_3925_ = leanh::lean_box(0);
                        v_isShared_3926_ = v_isSharedCheck_3930_;
                        state = 40;
                        continue;
                    }
                }
            }
            32 => {
                v___x_3853_ = (leanh::lean_unbox(v_a_3849_) as u8);
                leanh::lean_dec(v_a_3849_);
                if v___x_3853_ == 0 {
                    leanh::lean_del_object(v___x_3844_);
                    leanh::lean_dec(v_val_3842_);
                    leanh::lean_del_object(v___x_3835_);
                    leanh::lean_dec(v_snd_3833_);
                    leanh::lean_dec(v_fst_3832_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v___x_3854_ = leanh::lean_box(0);
                    if v_isShared_3852_ == 0 {
                        leanh::lean_ctor_set(v___x_3851_, 0, v___x_3854_);
                        v___x_3856_ = v___x_3851_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_3857_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3854_);
                        v___x_3856_ = v_reuseFailAlloc_3857_;
                        state = 33;
                        continue;
                    }
                } else {
                    v_u_3858_ = leanh::lean_ctor_get(v_a_3619_, 0);
                    v_type_3859_ = leanh::lean_ctor_get(v_a_3619_, 1);
                    v_fieldInst_3860_ = leanh::lean_ctor_get(v_a_3619_, 2);
                    v_isChar0Inst_3861_ = leanh::lean_ctor_get(v_a_3619_, 3);
                    leanh::lean_inc(v_fst_3832_);
                    v___x_3862_ = l_Rat_zpow(v_fst_3832_, v_val_3842_);
                    v___x_3863_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__34;
                    v___x_3864_ = leanh::lean_box(0);
                    leanh::lean_inc(v_u_3858_);
                    v___x_3865_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3865_, 0, v_u_3858_);
                    leanh::lean_ctor_set(v___x_3865_, 1, v___x_3864_);
                    v___x_3866_ = l_Lean_mkConst(v___x_3863_, v___x_3865_);
                    v___x_3911_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
                    v___x_3912_ = lean_int_dec_le(v___x_3911_, v_val_3842_);
                    if v___x_3912_ == 0 {
                        v___x_3913_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
                        v___x_3914_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
                        v___x_3915_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
                        v___x_3916_ = lean_int_neg(v_val_3842_);
                        leanh::lean_dec(v_val_3842_);
                        v___x_3917_ = l_Int_toNat(v___x_3916_);
                        leanh::lean_dec(v___x_3916_);
                        v___x_3918_ = l_Lean_instToExprInt_mkNat(v___x_3917_);
                        v___x_3919_ =
                            l_Lean_mkApp3(v___x_3913_, v___x_3914_, v___x_3915_, v___x_3918_);
                        v___y_3898_ = v___x_3919_;
                        state = 39;
                        continue;
                    } else {
                        v___x_3920_ = l_Int_toNat(v_val_3842_);
                        leanh::lean_dec(v_val_3842_);
                        v___x_3921_ = l_Lean_instToExprInt_mkNat(v___x_3920_);
                        v___y_3898_ = v___x_3921_;
                        state = 39;
                        continue;
                    }
                }
            }
            33 => {
                return v___x_3856_;
            }
            34 => {
                v___x_3871_ = l_Lean_eagerReflBoolTrue;
                leanh::lean_inc_ref(v_isChar0Inst_3861_);
                leanh::lean_inc_ref(v_fieldInst_3860_);
                leanh::lean_inc_ref(v_type_3859_);
                v___x_3872_ = l_Lean_mkApp9(
                    v___x_3866_,
                    v_type_3859_,
                    v_fieldInst_3860_,
                    v_isChar0Inst_3861_,
                    v_arg_3640_,
                    v___y_3869_,
                    v___y_3868_,
                    v___y_3870_,
                    v___x_3871_,
                    v_snd_3833_,
                );
                if v_isShared_3836_ == 0 {
                    leanh::lean_ctor_set(v___x_3835_, 1, v___x_3872_);
                    leanh::lean_ctor_set(v___x_3835_, 0, v___x_3862_);
                    v___x_3874_ = v___x_3835_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3881_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 0, v___x_3862_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3881_, 1, v___x_3872_);
                    v___x_3874_ = v_reuseFailAlloc_3881_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3845_ == 0 {
                    leanh::lean_ctor_set(v___x_3844_, 0, v___x_3874_);
                    v___x_3876_ = v___x_3844_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3880_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3880_, 0, v___x_3874_);
                    v___x_3876_ = v_reuseFailAlloc_3880_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_3852_ == 0 {
                    leanh::lean_ctor_set(v___x_3851_, 0, v___x_3876_);
                    v___x_3878_ = v___x_3851_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3879_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
                    v___x_3878_ = v_reuseFailAlloc_3879_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3878_;
            }
            38 => {
                v_num_3885_ = leanh::lean_ctor_get(v___x_3862_, 0);
                leanh::lean_inc(v_num_3885_);
                v_den_3886_ = leanh::lean_ctor_get(v___x_3862_, 1);
                leanh::lean_inc(v_den_3886_);
                v___x_3887_ = leanh::lean_unsigned_to_nat(1);
                v___x_3888_ = lean_nat_dec_eq(v_den_3886_, v___x_3887_);
                if v___x_3888_ == 0 {
                    v___x_3889_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_3890_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_3891_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_3892_ = l_Lean_instToExprRat_mkInt(v_num_3885_);
                    leanh::lean_dec(v_num_3885_);
                    v___x_3893_ = lean_nat_to_int(v_den_3886_);
                    v___x_3894_ = l_Lean_instToExprRat_mkInt(v___x_3893_);
                    leanh::lean_dec(v___x_3893_);
                    v___x_3895_ = l_Lean_mkApp6(
                        v___x_3889_,
                        v___x_3890_,
                        v___x_3890_,
                        v___x_3890_,
                        v___x_3891_,
                        v___x_3892_,
                        v___x_3894_,
                    );
                    v___y_3868_ = v___y_3884_;
                    v___y_3869_ = v___y_3883_;
                    v___y_3870_ = v___x_3895_;
                    state = 34;
                    continue;
                } else {
                    leanh::lean_dec(v_den_3886_);
                    v___x_3896_ = l_Lean_instToExprRat_mkInt(v_num_3885_);
                    leanh::lean_dec(v_num_3885_);
                    v___y_3868_ = v___y_3884_;
                    v___y_3869_ = v___y_3883_;
                    v___y_3870_ = v___x_3896_;
                    state = 34;
                    continue;
                }
            }
            39 => {
                v_num_3899_ = leanh::lean_ctor_get(v_fst_3832_, 0);
                leanh::lean_inc(v_num_3899_);
                v_den_3900_ = leanh::lean_ctor_get(v_fst_3832_, 1);
                leanh::lean_inc(v_den_3900_);
                leanh::lean_dec(v_fst_3832_);
                v___x_3901_ = leanh::lean_unsigned_to_nat(1);
                v___x_3902_ = lean_nat_dec_eq(v_den_3900_, v___x_3901_);
                if v___x_3902_ == 0 {
                    v___x_3903_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_3904_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_3905_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_3906_ = l_Lean_instToExprRat_mkInt(v_num_3899_);
                    leanh::lean_dec(v_num_3899_);
                    v___x_3907_ = lean_nat_to_int(v_den_3900_);
                    v___x_3908_ = l_Lean_instToExprRat_mkInt(v___x_3907_);
                    leanh::lean_dec(v___x_3907_);
                    v___x_3909_ = l_Lean_mkApp6(
                        v___x_3903_,
                        v___x_3904_,
                        v___x_3904_,
                        v___x_3904_,
                        v___x_3905_,
                        v___x_3906_,
                        v___x_3908_,
                    );
                    v___y_3883_ = v___y_3898_;
                    v___y_3884_ = v___x_3909_;
                    state = 38;
                    continue;
                } else {
                    leanh::lean_dec(v_den_3900_);
                    v___x_3910_ = l_Lean_instToExprRat_mkInt(v_num_3899_);
                    leanh::lean_dec(v_num_3899_);
                    v___y_3883_ = v___y_3898_;
                    v___y_3884_ = v___x_3910_;
                    state = 38;
                    continue;
                }
            }
            40 => {
                if v_isShared_3926_ == 0 {
                    v___x_3928_ = v___x_3925_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_3929_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
                    v___x_3928_ = v_reuseFailAlloc_3929_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_3928_;
            }
            42 => {
                return v___x_3934_;
            }
            43 => {
                if v_isShared_3940_ == 0 {
                    v___x_3942_ = v___x_3939_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_3943_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3943_, 0, v_a_3937_);
                    v___x_3942_ = v_reuseFailAlloc_3943_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_3942_;
            }
            45 => {
                if v_isShared_3950_ == 0 {
                    v___x_3952_ = v___x_3949_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_3952_;
            }
            47 => {
                v___x_3963_ = l_Lean_Meta_getNatValue_x3f(
                    v_arg_3637_,
                    v_a_3620_,
                    v_a_3621_,
                    v_a_3622_,
                    v_a_3623_,
                );
                leanh::lean_dec_ref(v_arg_3637_);
                if leanh::lean_obj_tag(v___x_3963_) == 0 {
                    v_a_3964_ = leanh::lean_ctor_get(v___x_3963_, 0);
                    v_isSharedCheck_4046_ = (!leanh::lean_is_exclusive(v___x_3963_)) as u8;
                    if v_isSharedCheck_4046_ == 0 {
                        v___x_3966_ = v___x_3963_;
                        v_isShared_3967_ = v_isSharedCheck_4046_;
                        state = 48;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3964_);
                        leanh::lean_dec(v___x_3963_);
                        v___x_3966_ = leanh::lean_box(0);
                        v_isShared_3967_ = v_isSharedCheck_4046_;
                        state = 48;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3961_);
                    leanh::lean_dec(v_snd_3959_);
                    leanh::lean_dec(v_fst_3958_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v_a_4047_ = leanh::lean_ctor_get(v___x_3963_, 0);
                    v_isSharedCheck_4054_ = (!leanh::lean_is_exclusive(v___x_3963_)) as u8;
                    if v_isSharedCheck_4054_ == 0 {
                        v___x_4049_ = v___x_3963_;
                        v_isShared_4050_ = v_isSharedCheck_4054_;
                        state = 60;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4047_);
                        leanh::lean_dec(v___x_3963_);
                        v___x_4049_ = leanh::lean_box(0);
                        v_isShared_4050_ = v_isSharedCheck_4054_;
                        state = 60;
                        continue;
                    }
                }
            }
            48 => {
                if leanh::lean_obj_tag(v_a_3964_) == 1 {
                    leanh::lean_del_object(v___x_3966_);
                    v_val_3968_ = leanh::lean_ctor_get(v_a_3964_, 0);
                    v_isSharedCheck_4041_ = (!leanh::lean_is_exclusive(v_a_3964_)) as u8;
                    if v_isSharedCheck_4041_ == 0 {
                        v___x_3970_ = v_a_3964_;
                        v_isShared_3971_ = v_isSharedCheck_4041_;
                        state = 49;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_3968_);
                        leanh::lean_dec(v_a_3964_);
                        v___x_3970_ = leanh::lean_box(0);
                        v_isShared_3971_ = v_isSharedCheck_4041_;
                        state = 49;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_3964_);
                    leanh::lean_del_object(v___x_3961_);
                    leanh::lean_dec(v_snd_3959_);
                    leanh::lean_dec(v_fst_3958_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v___x_4042_ = leanh::lean_box(0);
                    if v_isShared_3967_ == 0 {
                        leanh::lean_ctor_set(v___x_3966_, 0, v___x_4042_);
                        v___x_4044_ = v___x_3966_;
                        state = 59;
                        continue;
                    } else {
                        v_reuseFailAlloc_4045_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4045_, 0, v___x_4042_);
                        v___x_4044_ = v_reuseFailAlloc_4045_;
                        state = 59;
                        continue;
                    }
                }
            }
            49 => {
                leanh::lean_inc(v_val_3968_);
                v___x_3972_ = l_Lean_checkExponent(v_val_3968_, v___x_3654_, v_a_3622_, v_a_3623_);
                if leanh::lean_obj_tag(v___x_3972_) == 0 {
                    v_a_3973_ = leanh::lean_ctor_get(v___x_3972_, 0);
                    v_isSharedCheck_4032_ = (!leanh::lean_is_exclusive(v___x_3972_)) as u8;
                    if v_isSharedCheck_4032_ == 0 {
                        v___x_3975_ = v___x_3972_;
                        v_isShared_3976_ = v_isSharedCheck_4032_;
                        state = 50;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_3973_);
                        leanh::lean_dec(v___x_3972_);
                        v___x_3975_ = leanh::lean_box(0);
                        v_isShared_3976_ = v_isSharedCheck_4032_;
                        state = 50;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_3970_);
                    leanh::lean_dec(v_val_3968_);
                    leanh::lean_del_object(v___x_3961_);
                    leanh::lean_dec(v_snd_3959_);
                    leanh::lean_dec(v_fst_3958_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v_a_4033_ = leanh::lean_ctor_get(v___x_3972_, 0);
                    v_isSharedCheck_4040_ = (!leanh::lean_is_exclusive(v___x_3972_)) as u8;
                    if v_isSharedCheck_4040_ == 0 {
                        v___x_4035_ = v___x_3972_;
                        v_isShared_4036_ = v_isSharedCheck_4040_;
                        state = 57;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4033_);
                        leanh::lean_dec(v___x_3972_);
                        v___x_4035_ = leanh::lean_box(0);
                        v_isShared_4036_ = v_isSharedCheck_4040_;
                        state = 57;
                        continue;
                    }
                }
            }
            50 => {
                v___x_3977_ = (leanh::lean_unbox(v_a_3973_) as u8);
                leanh::lean_dec(v_a_3973_);
                if v___x_3977_ == 0 {
                    leanh::lean_del_object(v___x_3970_);
                    leanh::lean_dec(v_val_3968_);
                    leanh::lean_del_object(v___x_3961_);
                    leanh::lean_dec(v_snd_3959_);
                    leanh::lean_dec(v_fst_3958_);
                    leanh::lean_dec_ref(v_arg_3640_);
                    v___x_3978_ = leanh::lean_box(0);
                    if v_isShared_3976_ == 0 {
                        leanh::lean_ctor_set(v___x_3975_, 0, v___x_3978_);
                        v___x_3980_ = v___x_3975_;
                        state = 51;
                        continue;
                    } else {
                        v_reuseFailAlloc_3981_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
                        v___x_3980_ = v_reuseFailAlloc_3981_;
                        state = 51;
                        continue;
                    }
                } else {
                    v_u_3982_ = leanh::lean_ctor_get(v_a_3619_, 0);
                    v_type_3983_ = leanh::lean_ctor_get(v_a_3619_, 1);
                    v_fieldInst_3984_ = leanh::lean_ctor_get(v_a_3619_, 2);
                    v_isChar0Inst_3985_ = leanh::lean_ctor_get(v_a_3619_, 3);
                    v_num_3986_ = leanh::lean_ctor_get(v_fst_3958_, 0);
                    leanh::lean_inc(v_num_3986_);
                    v_den_3987_ = leanh::lean_ctor_get(v_fst_3958_, 1);
                    leanh::lean_inc(v_den_3987_);
                    v___x_3988_ = l_Rat_pow(v_fst_3958_, v_val_3968_);
                    v___x_3989_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__44;
                    v___x_3990_ = leanh::lean_box(0);
                    leanh::lean_inc(v_u_3982_);
                    v___x_3991_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_3991_, 0, v_u_3982_);
                    leanh::lean_ctor_set(v___x_3991_, 1, v___x_3990_);
                    v___x_3992_ = l_Lean_mkConst(v___x_3989_, v___x_3991_);
                    v___x_3993_ = l_Lean_mkNatLit(v_val_3968_);
                    v___x_4022_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4023_ = lean_nat_dec_eq(v_den_3987_, v___x_4022_);
                    if v___x_4023_ == 0 {
                        v___x_4024_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                        v___x_4025_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                        v___x_4026_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                        v___x_4027_ = l_Lean_instToExprRat_mkInt(v_num_3986_);
                        leanh::lean_dec(v_num_3986_);
                        v___x_4028_ = lean_nat_to_int(v_den_3987_);
                        v___x_4029_ = l_Lean_instToExprRat_mkInt(v___x_4028_);
                        leanh::lean_dec(v___x_4028_);
                        v___x_4030_ = l_Lean_mkApp6(
                            v___x_4024_,
                            v___x_4025_,
                            v___x_4025_,
                            v___x_4025_,
                            v___x_4026_,
                            v___x_4027_,
                            v___x_4029_,
                        );
                        v___y_4009_ = v___x_4030_;
                        state = 56;
                        continue;
                    } else {
                        leanh::lean_dec(v_den_3987_);
                        v___x_4031_ = l_Lean_instToExprRat_mkInt(v_num_3986_);
                        leanh::lean_dec(v_num_3986_);
                        v___y_4009_ = v___x_4031_;
                        state = 56;
                        continue;
                    }
                }
            }
            51 => {
                return v___x_3980_;
            }
            52 => {
                v___x_3997_ = l_Lean_eagerReflBoolTrue;
                leanh::lean_inc_ref(v_isChar0Inst_3985_);
                leanh::lean_inc_ref(v_fieldInst_3984_);
                leanh::lean_inc_ref(v_type_3983_);
                v___x_3998_ = l_Lean_mkApp9(
                    v___x_3992_,
                    v_type_3983_,
                    v_fieldInst_3984_,
                    v_isChar0Inst_3985_,
                    v_arg_3640_,
                    v___x_3993_,
                    v___y_3995_,
                    v___y_3996_,
                    v___x_3997_,
                    v_snd_3959_,
                );
                if v_isShared_3962_ == 0 {
                    leanh::lean_ctor_set(v___x_3961_, 1, v___x_3998_);
                    leanh::lean_ctor_set(v___x_3961_, 0, v___x_3988_);
                    v___x_4000_ = v___x_3961_;
                    state = 53;
                    continue;
                } else {
                    v_reuseFailAlloc_4007_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_3988_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4007_, 1, v___x_3998_);
                    v___x_4000_ = v_reuseFailAlloc_4007_;
                    state = 53;
                    continue;
                }
            }
            53 => {
                if v_isShared_3971_ == 0 {
                    leanh::lean_ctor_set(v___x_3970_, 0, v___x_4000_);
                    v___x_4002_ = v___x_3970_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4000_);
                    v___x_4002_ = v_reuseFailAlloc_4006_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                if v_isShared_3976_ == 0 {
                    leanh::lean_ctor_set(v___x_3975_, 0, v___x_4002_);
                    v___x_4004_ = v___x_3975_;
                    state = 55;
                    continue;
                } else {
                    v_reuseFailAlloc_4005_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4005_, 0, v___x_4002_);
                    v___x_4004_ = v_reuseFailAlloc_4005_;
                    state = 55;
                    continue;
                }
            }
            55 => {
                return v___x_4004_;
            }
            56 => {
                v_num_4010_ = leanh::lean_ctor_get(v___x_3988_, 0);
                leanh::lean_inc(v_num_4010_);
                v_den_4011_ = leanh::lean_ctor_get(v___x_3988_, 1);
                leanh::lean_inc(v_den_4011_);
                v___x_4012_ = leanh::lean_unsigned_to_nat(1);
                v___x_4013_ = lean_nat_dec_eq(v_den_4011_, v___x_4012_);
                if v___x_4013_ == 0 {
                    v___x_4014_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_4015_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_4016_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_4017_ = l_Lean_instToExprRat_mkInt(v_num_4010_);
                    leanh::lean_dec(v_num_4010_);
                    v___x_4018_ = lean_nat_to_int(v_den_4011_);
                    v___x_4019_ = l_Lean_instToExprRat_mkInt(v___x_4018_);
                    leanh::lean_dec(v___x_4018_);
                    v___x_4020_ = l_Lean_mkApp6(
                        v___x_4014_,
                        v___x_4015_,
                        v___x_4015_,
                        v___x_4015_,
                        v___x_4016_,
                        v___x_4017_,
                        v___x_4019_,
                    );
                    v___y_3995_ = v___y_4009_;
                    v___y_3996_ = v___x_4020_;
                    state = 52;
                    continue;
                } else {
                    leanh::lean_dec(v_den_4011_);
                    v___x_4021_ = l_Lean_instToExprRat_mkInt(v_num_4010_);
                    leanh::lean_dec(v_num_4010_);
                    v___y_3995_ = v___y_4009_;
                    v___y_3996_ = v___x_4021_;
                    state = 52;
                    continue;
                }
            }
            57 => {
                if v_isShared_4036_ == 0 {
                    v___x_4038_ = v___x_4035_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_4039_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4033_);
                    v___x_4038_ = v_reuseFailAlloc_4039_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_4038_;
            }
            59 => {
                return v___x_4044_;
            }
            60 => {
                if v_isShared_4050_ == 0 {
                    v___x_4052_ = v___x_4049_;
                    state = 61;
                    continue;
                } else {
                    v_reuseFailAlloc_4053_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
                    v___x_4052_ = v_reuseFailAlloc_4053_;
                    state = 61;
                    continue;
                }
            }
            61 => {
                return v___x_4052_;
            }
            62 => {
                if v_isShared_4060_ == 0 {
                    v___x_4062_ = v___x_4059_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                return v___x_4062_;
            }
            64 => {
                if leanh::lean_obj_tag(v_a_4066_) == 0 {
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_4070_ = leanh::lean_box(0);
                    if v_isShared_4069_ == 0 {
                        leanh::lean_ctor_set(v___x_4068_, 0, v___x_4070_);
                        v___x_4072_ = v___x_4068_;
                        state = 65;
                        continue;
                    } else {
                        v_reuseFailAlloc_4073_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4073_, 0, v___x_4070_);
                        v___x_4072_ = v_reuseFailAlloc_4073_;
                        state = 65;
                        continue;
                    }
                } else {
                    v_val_4074_ = leanh::lean_ctor_get(v_a_4066_, 0);
                    leanh::lean_inc(v_val_4074_);
                    leanh::lean_dec_ref_known(v_a_4066_, 1);
                    v___x_4075_ = (leanh::lean_unbox(v_val_4074_) as u8);
                    leanh::lean_dec(v_val_4074_);
                    if v___x_4075_ == 0 {
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_4076_ = leanh::lean_box(0);
                        if v_isShared_4069_ == 0 {
                            leanh::lean_ctor_set(v___x_4068_, 0, v___x_4076_);
                            v___x_4078_ = v___x_4068_;
                            state = 66;
                            continue;
                        } else {
                            v_reuseFailAlloc_4079_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4079_, 0, v___x_4076_);
                            v___x_4078_ = v_reuseFailAlloc_4079_;
                            state = 66;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4068_);
                        leanh::lean_inc_ref(v_arg_3637_);
                        v___x_4080_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3637_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_4080_) == 0 {
                            v_a_4081_ = leanh::lean_ctor_get(v___x_4080_, 0);
                            leanh::lean_inc(v_a_4081_);
                            if leanh::lean_obj_tag(v_a_4081_) == 0 {
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_4080_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_4080_, 1);
                                v_val_4082_ = leanh::lean_ctor_get(v_a_4081_, 0);
                                leanh::lean_inc(v_val_4082_);
                                leanh::lean_dec_ref_known(v_a_4081_, 1);
                                v___f_4083_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__45;
                                v___x_4084_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__47;
                                v___x_4085_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_4084_, v_arg_3637_, v_val_4082_, v___f_4083_, v_a_3619_);
                                return v___x_4085_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_4080_;
                        }
                    }
                }
            }
            65 => {
                return v___x_4072_;
            }
            66 => {
                return v___x_4078_;
            }
            67 => {
                if v_isShared_4090_ == 0 {
                    v___x_4092_ = v___x_4089_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_4093_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4093_, 0, v_a_4087_);
                    v___x_4092_ = v_reuseFailAlloc_4093_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_4092_;
            }
            69 => {
                if leanh::lean_obj_tag(v_a_4096_) == 0 {
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_4100_ = leanh::lean_box(0);
                    if v_isShared_4099_ == 0 {
                        leanh::lean_ctor_set(v___x_4098_, 0, v___x_4100_);
                        v___x_4102_ = v___x_4098_;
                        state = 70;
                        continue;
                    } else {
                        v_reuseFailAlloc_4103_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4100_);
                        v___x_4102_ = v_reuseFailAlloc_4103_;
                        state = 70;
                        continue;
                    }
                } else {
                    v_val_4104_ = leanh::lean_ctor_get(v_a_4096_, 0);
                    leanh::lean_inc(v_val_4104_);
                    leanh::lean_dec_ref_known(v_a_4096_, 1);
                    v___x_4105_ = (leanh::lean_unbox(v_val_4104_) as u8);
                    leanh::lean_dec(v_val_4104_);
                    if v___x_4105_ == 0 {
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_4106_ = leanh::lean_box(0);
                        if v_isShared_4099_ == 0 {
                            leanh::lean_ctor_set(v___x_4098_, 0, v___x_4106_);
                            v___x_4108_ = v___x_4098_;
                            state = 71;
                            continue;
                        } else {
                            v_reuseFailAlloc_4109_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4106_);
                            v___x_4108_ = v_reuseFailAlloc_4109_;
                            state = 71;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4098_);
                        leanh::lean_inc_ref(v_arg_3637_);
                        v___x_4110_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_arg_3637_, v_a_3619_, v_a_3620_, v_a_3621_, v_a_3622_, v_a_3623_);
                        if leanh::lean_obj_tag(v___x_4110_) == 0 {
                            v_a_4111_ = leanh::lean_ctor_get(v___x_4110_, 0);
                            leanh::lean_inc(v_a_4111_);
                            if leanh::lean_obj_tag(v_a_4111_) == 0 {
                                leanh::lean_dec_ref(v_arg_3637_);
                                return v___x_4110_;
                            } else {
                                leanh::lean_dec_ref_known(v___x_4110_, 1);
                                v_val_4112_ = leanh::lean_ctor_get(v_a_4111_, 0);
                                leanh::lean_inc(v_val_4112_);
                                leanh::lean_dec_ref_known(v_a_4111_, 1);
                                v___f_4113_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__48;
                                v___x_4114_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__50;
                                v___x_4115_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkUnary___redArg(v___x_4114_, v_arg_3637_, v_val_4112_, v___f_4113_, v_a_3619_);
                                return v___x_4115_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_arg_3637_);
                            return v___x_4110_;
                        }
                    }
                }
            }
            70 => {
                return v___x_4102_;
            }
            71 => {
                return v___x_4108_;
            }
            72 => {
                if v_isShared_4120_ == 0 {
                    v___x_4122_ = v___x_4119_;
                    state = 73;
                    continue;
                } else {
                    v_reuseFailAlloc_4123_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
                    v___x_4122_ = v_reuseFailAlloc_4123_;
                    state = 73;
                    continue;
                }
            }
            73 => {
                return v___x_4122_;
            }
            74 => {
                if leanh::lean_obj_tag(v_a_4126_) == 0 {
                    leanh::lean_dec_ref(v_arg_3640_);
                    v___x_4130_ = leanh::lean_box(0);
                    if v_isShared_4129_ == 0 {
                        leanh::lean_ctor_set(v___x_4128_, 0, v___x_4130_);
                        v___x_4132_ = v___x_4128_;
                        state = 75;
                        continue;
                    } else {
                        v_reuseFailAlloc_4133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
                        v___x_4132_ = v_reuseFailAlloc_4133_;
                        state = 75;
                        continue;
                    }
                } else {
                    v_val_4134_ = leanh::lean_ctor_get(v_a_4126_, 0);
                    leanh::lean_inc(v_val_4134_);
                    leanh::lean_dec_ref_known(v_a_4126_, 1);
                    v___x_4135_ = (leanh::lean_unbox(v_val_4134_) as u8);
                    leanh::lean_dec(v_val_4134_);
                    if v___x_4135_ == 0 {
                        leanh::lean_dec_ref(v_arg_3640_);
                        v___x_4136_ = leanh::lean_box(0);
                        if v_isShared_4129_ == 0 {
                            leanh::lean_ctor_set(v___x_4128_, 0, v___x_4136_);
                            v___x_4138_ = v___x_4128_;
                            state = 76;
                            continue;
                        } else {
                            v_reuseFailAlloc_4139_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                            v___x_4138_ = v_reuseFailAlloc_4139_;
                            state = 76;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4128_);
                        v___x_4140_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_3640_,
                            v_a_3620_,
                            v_a_3621_,
                            v_a_3622_,
                            v_a_3623_,
                        );
                        leanh::lean_dec_ref(v_arg_3640_);
                        if leanh::lean_obj_tag(v___x_4140_) == 0 {
                            v_a_4141_ = leanh::lean_ctor_get(v___x_4140_, 0);
                            v_isSharedCheck_4171_ =
                                (!leanh::lean_is_exclusive(v___x_4140_)) as u8;
                            if v_isSharedCheck_4171_ == 0 {
                                v___x_4143_ = v___x_4140_;
                                v_isShared_4144_ = v_isSharedCheck_4171_;
                                state = 77;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4141_);
                                leanh::lean_dec(v___x_4140_);
                                v___x_4143_ = leanh::lean_box(0);
                                v_isShared_4144_ = v_isSharedCheck_4171_;
                                state = 77;
                                continue;
                            }
                        } else {
                            v_a_4172_ = leanh::lean_ctor_get(v___x_4140_, 0);
                            v_isSharedCheck_4179_ =
                                (!leanh::lean_is_exclusive(v___x_4140_)) as u8;
                            if v_isSharedCheck_4179_ == 0 {
                                v___x_4174_ = v___x_4140_;
                                v_isShared_4175_ = v_isSharedCheck_4179_;
                                state = 82;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4172_);
                                leanh::lean_dec(v___x_4140_);
                                v___x_4174_ = leanh::lean_box(0);
                                v_isShared_4175_ = v_isSharedCheck_4179_;
                                state = 82;
                                continue;
                            }
                        }
                    }
                }
            }
            75 => {
                return v___x_4132_;
            }
            76 => {
                return v___x_4138_;
            }
            77 => {
                if leanh::lean_obj_tag(v_a_4141_) == 1 {
                    v_val_4145_ = leanh::lean_ctor_get(v_a_4141_, 0);
                    v_isSharedCheck_4166_ = (!leanh::lean_is_exclusive(v_a_4141_)) as u8;
                    if v_isSharedCheck_4166_ == 0 {
                        v___x_4147_ = v_a_4141_;
                        v_isShared_4148_ = v_isSharedCheck_4166_;
                        state = 78;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4145_);
                        leanh::lean_dec(v_a_4141_);
                        v___x_4147_ = leanh::lean_box(0);
                        v_isShared_4148_ = v_isSharedCheck_4166_;
                        state = 78;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4141_);
                    v___x_4167_ = leanh::lean_box(0);
                    if v_isShared_4144_ == 0 {
                        leanh::lean_ctor_set(v___x_4143_, 0, v___x_4167_);
                        v___x_4169_ = v___x_4143_;
                        state = 81;
                        continue;
                    } else {
                        v_reuseFailAlloc_4170_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4167_);
                        v___x_4169_ = v_reuseFailAlloc_4170_;
                        state = 81;
                        continue;
                    }
                }
            }
            78 => {
                v_u_4149_ = leanh::lean_ctor_get(v_a_3619_, 0);
                v_type_4150_ = leanh::lean_ctor_get(v_a_3619_, 1);
                v_fieldInst_4151_ = leanh::lean_ctor_get(v_a_3619_, 2);
                v___x_4152_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__52;
                v___x_4153_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_4149_);
                v___x_4154_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4154_, 0, v_u_4149_);
                leanh::lean_ctor_set(v___x_4154_, 1, v___x_4153_);
                v___x_4155_ = l_Lean_mkConst(v___x_4152_, v___x_4154_);
                leanh::lean_inc(v_val_4145_);
                v___x_4156_ = l_Lean_mkNatLit(v_val_4145_);
                leanh::lean_inc_ref(v_fieldInst_4151_);
                leanh::lean_inc_ref(v_type_4150_);
                v___x_4157_ =
                    l_Lean_mkApp3(v___x_4155_, v_type_4150_, v_fieldInst_4151_, v___x_4156_);
                v___x_4158_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_4145_);
                v___x_4159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4159_, 0, v___x_4158_);
                leanh::lean_ctor_set(v___x_4159_, 1, v___x_4157_);
                if v_isShared_4148_ == 0 {
                    leanh::lean_ctor_set(v___x_4147_, 0, v___x_4159_);
                    v___x_4161_ = v___x_4147_;
                    state = 79;
                    continue;
                } else {
                    v_reuseFailAlloc_4165_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4159_);
                    v___x_4161_ = v_reuseFailAlloc_4165_;
                    state = 79;
                    continue;
                }
            }
            79 => {
                if v_isShared_4144_ == 0 {
                    leanh::lean_ctor_set(v___x_4143_, 0, v___x_4161_);
                    v___x_4163_ = v___x_4143_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_4164_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4161_);
                    v___x_4163_ = v_reuseFailAlloc_4164_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                return v___x_4163_;
            }
            81 => {
                return v___x_4169_;
            }
            82 => {
                if v_isShared_4175_ == 0 {
                    v___x_4177_ = v___x_4174_;
                    state = 83;
                    continue;
                } else {
                    v_reuseFailAlloc_4178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4178_, 0, v_a_4172_);
                    v___x_4177_ = v_reuseFailAlloc_4178_;
                    state = 83;
                    continue;
                }
            }
            83 => {
                return v___x_4177_;
            }
            84 => {
                if v_isShared_4184_ == 0 {
                    v___x_4186_ = v___x_4183_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_4187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
                    v___x_4186_ = v_reuseFailAlloc_4187_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                return v___x_4186_;
            }
            86 => {
                if leanh::lean_obj_tag(v_a_4190_) == 0 {
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_4194_ = leanh::lean_box(0);
                    if v_isShared_4193_ == 0 {
                        leanh::lean_ctor_set(v___x_4192_, 0, v___x_4194_);
                        v___x_4196_ = v___x_4192_;
                        state = 87;
                        continue;
                    } else {
                        v_reuseFailAlloc_4197_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4197_, 0, v___x_4194_);
                        v___x_4196_ = v_reuseFailAlloc_4197_;
                        state = 87;
                        continue;
                    }
                } else {
                    v_val_4198_ = leanh::lean_ctor_get(v_a_4190_, 0);
                    leanh::lean_inc(v_val_4198_);
                    leanh::lean_dec_ref_known(v_a_4190_, 1);
                    v___x_4199_ = (leanh::lean_unbox(v_val_4198_) as u8);
                    leanh::lean_dec(v_val_4198_);
                    if v___x_4199_ == 0 {
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_4200_ = leanh::lean_box(0);
                        if v_isShared_4193_ == 0 {
                            leanh::lean_ctor_set(v___x_4192_, 0, v___x_4200_);
                            v___x_4202_ = v___x_4192_;
                            state = 88;
                            continue;
                        } else {
                            v_reuseFailAlloc_4203_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4203_, 0, v___x_4200_);
                            v___x_4202_ = v_reuseFailAlloc_4203_;
                            state = 88;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4192_);
                        v___x_4204_ = l_Lean_Meta_getNatValue_x3f(
                            v_arg_3637_,
                            v_a_3620_,
                            v_a_3621_,
                            v_a_3622_,
                            v_a_3623_,
                        );
                        leanh::lean_dec_ref(v_arg_3637_);
                        if leanh::lean_obj_tag(v___x_4204_) == 0 {
                            v_a_4205_ = leanh::lean_ctor_get(v___x_4204_, 0);
                            v_isSharedCheck_4235_ =
                                (!leanh::lean_is_exclusive(v___x_4204_)) as u8;
                            if v_isSharedCheck_4235_ == 0 {
                                v___x_4207_ = v___x_4204_;
                                v_isShared_4208_ = v_isSharedCheck_4235_;
                                state = 89;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4205_);
                                leanh::lean_dec(v___x_4204_);
                                v___x_4207_ = leanh::lean_box(0);
                                v_isShared_4208_ = v_isSharedCheck_4235_;
                                state = 89;
                                continue;
                            }
                        } else {
                            v_a_4236_ = leanh::lean_ctor_get(v___x_4204_, 0);
                            v_isSharedCheck_4243_ =
                                (!leanh::lean_is_exclusive(v___x_4204_)) as u8;
                            if v_isSharedCheck_4243_ == 0 {
                                v___x_4238_ = v___x_4204_;
                                v_isShared_4239_ = v_isSharedCheck_4243_;
                                state = 94;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4236_);
                                leanh::lean_dec(v___x_4204_);
                                v___x_4238_ = leanh::lean_box(0);
                                v_isShared_4239_ = v_isSharedCheck_4243_;
                                state = 94;
                                continue;
                            }
                        }
                    }
                }
            }
            87 => {
                return v___x_4196_;
            }
            88 => {
                return v___x_4202_;
            }
            89 => {
                if leanh::lean_obj_tag(v_a_4205_) == 1 {
                    v_val_4209_ = leanh::lean_ctor_get(v_a_4205_, 0);
                    v_isSharedCheck_4230_ = (!leanh::lean_is_exclusive(v_a_4205_)) as u8;
                    if v_isSharedCheck_4230_ == 0 {
                        v___x_4211_ = v_a_4205_;
                        v_isShared_4212_ = v_isSharedCheck_4230_;
                        state = 90;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4209_);
                        leanh::lean_dec(v_a_4205_);
                        v___x_4211_ = leanh::lean_box(0);
                        v_isShared_4212_ = v_isSharedCheck_4230_;
                        state = 90;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4205_);
                    v___x_4231_ = leanh::lean_box(0);
                    if v_isShared_4208_ == 0 {
                        leanh::lean_ctor_set(v___x_4207_, 0, v___x_4231_);
                        v___x_4233_ = v___x_4207_;
                        state = 93;
                        continue;
                    } else {
                        v_reuseFailAlloc_4234_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4234_, 0, v___x_4231_);
                        v___x_4233_ = v_reuseFailAlloc_4234_;
                        state = 93;
                        continue;
                    }
                }
            }
            90 => {
                v_u_4213_ = leanh::lean_ctor_get(v_a_3619_, 0);
                v_type_4214_ = leanh::lean_ctor_get(v_a_3619_, 1);
                v_fieldInst_4215_ = leanh::lean_ctor_get(v_a_3619_, 2);
                v___x_4216_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__54;
                v___x_4217_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_4213_);
                v___x_4218_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4218_, 0, v_u_4213_);
                leanh::lean_ctor_set(v___x_4218_, 1, v___x_4217_);
                v___x_4219_ = l_Lean_mkConst(v___x_4216_, v___x_4218_);
                leanh::lean_inc(v_val_4209_);
                v___x_4220_ = l_Lean_mkNatLit(v_val_4209_);
                leanh::lean_inc_ref(v_fieldInst_4215_);
                leanh::lean_inc_ref(v_type_4214_);
                v___x_4221_ =
                    l_Lean_mkApp3(v___x_4219_, v_type_4214_, v_fieldInst_4215_, v___x_4220_);
                v___x_4222_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval_spec__0(v_val_4209_);
                v___x_4223_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4223_, 0, v___x_4222_);
                leanh::lean_ctor_set(v___x_4223_, 1, v___x_4221_);
                if v_isShared_4212_ == 0 {
                    leanh::lean_ctor_set(v___x_4211_, 0, v___x_4223_);
                    v___x_4225_ = v___x_4211_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_4229_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4229_, 0, v___x_4223_);
                    v___x_4225_ = v_reuseFailAlloc_4229_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                if v_isShared_4208_ == 0 {
                    leanh::lean_ctor_set(v___x_4207_, 0, v___x_4225_);
                    v___x_4227_ = v___x_4207_;
                    state = 92;
                    continue;
                } else {
                    v_reuseFailAlloc_4228_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4228_, 0, v___x_4225_);
                    v___x_4227_ = v_reuseFailAlloc_4228_;
                    state = 92;
                    continue;
                }
            }
            92 => {
                return v___x_4227_;
            }
            93 => {
                return v___x_4233_;
            }
            94 => {
                if v_isShared_4239_ == 0 {
                    v___x_4241_ = v___x_4238_;
                    state = 95;
                    continue;
                } else {
                    v_reuseFailAlloc_4242_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4242_, 0, v_a_4236_);
                    v___x_4241_ = v_reuseFailAlloc_4242_;
                    state = 95;
                    continue;
                }
            }
            95 => {
                return v___x_4241_;
            }
            96 => {
                if v_isShared_4248_ == 0 {
                    v___x_4250_ = v___x_4247_;
                    state = 97;
                    continue;
                } else {
                    v_reuseFailAlloc_4251_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_a_4245_);
                    v___x_4250_ = v_reuseFailAlloc_4251_;
                    state = 97;
                    continue;
                }
            }
            97 => {
                return v___x_4250_;
            }
            98 => {
                if leanh::lean_obj_tag(v_a_4254_) == 0 {
                    leanh::lean_dec_ref(v_arg_3637_);
                    v___x_4258_ = leanh::lean_box(0);
                    if v_isShared_4257_ == 0 {
                        leanh::lean_ctor_set(v___x_4256_, 0, v___x_4258_);
                        v___x_4260_ = v___x_4256_;
                        state = 99;
                        continue;
                    } else {
                        v_reuseFailAlloc_4261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4261_, 0, v___x_4258_);
                        v___x_4260_ = v_reuseFailAlloc_4261_;
                        state = 99;
                        continue;
                    }
                } else {
                    v_val_4262_ = leanh::lean_ctor_get(v_a_4254_, 0);
                    leanh::lean_inc(v_val_4262_);
                    leanh::lean_dec_ref_known(v_a_4254_, 1);
                    v___x_4263_ = (leanh::lean_unbox(v_val_4262_) as u8);
                    leanh::lean_dec(v_val_4262_);
                    if v___x_4263_ == 0 {
                        leanh::lean_dec_ref(v_arg_3637_);
                        v___x_4264_ = leanh::lean_box(0);
                        if v_isShared_4257_ == 0 {
                            leanh::lean_ctor_set(v___x_4256_, 0, v___x_4264_);
                            v___x_4266_ = v___x_4256_;
                            state = 100;
                            continue;
                        } else {
                            v_reuseFailAlloc_4267_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
                            v___x_4266_ = v_reuseFailAlloc_4267_;
                            state = 100;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4256_);
                        v___x_4268_ = l_Lean_Meta_getIntValue_x3f(
                            v_arg_3637_,
                            v_a_3620_,
                            v_a_3621_,
                            v_a_3622_,
                            v_a_3623_,
                        );
                        if leanh::lean_obj_tag(v___x_4268_) == 0 {
                            v_a_4269_ = leanh::lean_ctor_get(v___x_4268_, 0);
                            v_isSharedCheck_4311_ =
                                (!leanh::lean_is_exclusive(v___x_4268_)) as u8;
                            if v_isSharedCheck_4311_ == 0 {
                                v___x_4271_ = v___x_4268_;
                                v_isShared_4272_ = v_isSharedCheck_4311_;
                                state = 101;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4269_);
                                leanh::lean_dec(v___x_4268_);
                                v___x_4271_ = leanh::lean_box(0);
                                v_isShared_4272_ = v_isSharedCheck_4311_;
                                state = 101;
                                continue;
                            }
                        } else {
                            v_a_4312_ = leanh::lean_ctor_get(v___x_4268_, 0);
                            v_isSharedCheck_4319_ =
                                (!leanh::lean_is_exclusive(v___x_4268_)) as u8;
                            if v_isSharedCheck_4319_ == 0 {
                                v___x_4314_ = v___x_4268_;
                                v_isShared_4315_ = v_isSharedCheck_4319_;
                                state = 107;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4312_);
                                leanh::lean_dec(v___x_4268_);
                                v___x_4314_ = leanh::lean_box(0);
                                v_isShared_4315_ = v_isSharedCheck_4319_;
                                state = 107;
                                continue;
                            }
                        }
                    }
                }
            }
            99 => {
                return v___x_4260_;
            }
            100 => {
                return v___x_4266_;
            }
            101 => {
                if leanh::lean_obj_tag(v_a_4269_) == 1 {
                    v_val_4273_ = leanh::lean_ctor_get(v_a_4269_, 0);
                    v_isSharedCheck_4306_ = (!leanh::lean_is_exclusive(v_a_4269_)) as u8;
                    if v_isSharedCheck_4306_ == 0 {
                        v___x_4275_ = v_a_4269_;
                        v_isShared_4276_ = v_isSharedCheck_4306_;
                        state = 102;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_4273_);
                        leanh::lean_dec(v_a_4269_);
                        v___x_4275_ = leanh::lean_box(0);
                        v_isShared_4276_ = v_isSharedCheck_4306_;
                        state = 102;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_4269_);
                    v___x_4307_ = leanh::lean_box(0);
                    if v_isShared_4272_ == 0 {
                        leanh::lean_ctor_set(v___x_4271_, 0, v___x_4307_);
                        v___x_4309_ = v___x_4271_;
                        state = 106;
                        continue;
                    } else {
                        v_reuseFailAlloc_4310_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4307_);
                        v___x_4309_ = v_reuseFailAlloc_4310_;
                        state = 106;
                        continue;
                    }
                }
            }
            102 => {
                v_u_4277_ = leanh::lean_ctor_get(v_a_3619_, 0);
                v_type_4278_ = leanh::lean_ctor_get(v_a_3619_, 1);
                v_fieldInst_4279_ = leanh::lean_ctor_get(v_a_3619_, 2);
                v___x_4280_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__56;
                v___x_4281_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_4277_);
                v___x_4282_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4282_, 0, v_u_4277_);
                leanh::lean_ctor_set(v___x_4282_, 1, v___x_4281_);
                v___x_4283_ = l_Lean_mkConst(v___x_4280_, v___x_4282_);
                v___x_4295_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
                v___x_4296_ = lean_int_dec_le(v___x_4295_, v_val_4273_);
                if v___x_4296_ == 0 {
                    v___x_4297_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
                    v___x_4298_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
                    v___x_4299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
                    v___x_4300_ = lean_int_neg(v_val_4273_);
                    v___x_4301_ = l_Int_toNat(v___x_4300_);
                    leanh::lean_dec(v___x_4300_);
                    v___x_4302_ = l_Lean_instToExprInt_mkNat(v___x_4301_);
                    v___x_4303_ = l_Lean_mkApp3(v___x_4297_, v___x_4298_, v___x_4299_, v___x_4302_);
                    v___y_4285_ = v___x_4303_;
                    state = 103;
                    continue;
                } else {
                    v___x_4304_ = l_Int_toNat(v_val_4273_);
                    v___x_4305_ = l_Lean_instToExprInt_mkNat(v___x_4304_);
                    v___y_4285_ = v___x_4305_;
                    state = 103;
                    continue;
                }
            }
            103 => {
                leanh::lean_inc_ref(v_fieldInst_4279_);
                leanh::lean_inc_ref(v_type_4278_);
                v___x_4286_ =
                    l_Lean_mkApp3(v___x_4283_, v_type_4278_, v_fieldInst_4279_, v___y_4285_);
                v___x_4287_ = l_Rat_ofInt(v_val_4273_);
                v___x_4288_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4288_, 0, v___x_4287_);
                leanh::lean_ctor_set(v___x_4288_, 1, v___x_4286_);
                if v_isShared_4276_ == 0 {
                    leanh::lean_ctor_set(v___x_4275_, 0, v___x_4288_);
                    v___x_4290_ = v___x_4275_;
                    state = 104;
                    continue;
                } else {
                    v_reuseFailAlloc_4294_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4294_, 0, v___x_4288_);
                    v___x_4290_ = v_reuseFailAlloc_4294_;
                    state = 104;
                    continue;
                }
            }
            104 => {
                if v_isShared_4272_ == 0 {
                    leanh::lean_ctor_set(v___x_4271_, 0, v___x_4290_);
                    v___x_4292_ = v___x_4271_;
                    state = 105;
                    continue;
                } else {
                    v_reuseFailAlloc_4293_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4293_, 0, v___x_4290_);
                    v___x_4292_ = v_reuseFailAlloc_4293_;
                    state = 105;
                    continue;
                }
            }
            105 => {
                return v___x_4292_;
            }
            106 => {
                return v___x_4309_;
            }
            107 => {
                if v_isShared_4315_ == 0 {
                    v___x_4317_ = v___x_4314_;
                    state = 108;
                    continue;
                } else {
                    v_reuseFailAlloc_4318_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4318_, 0, v_a_4312_);
                    v___x_4317_ = v_reuseFailAlloc_4318_;
                    state = 108;
                    continue;
                }
            }
            108 => {
                return v___x_4317_;
            }
            109 => {
                if v_isShared_4324_ == 0 {
                    v___x_4326_ = v___x_4323_;
                    state = 110;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_a_4321_);
                    v___x_4326_ = v_reuseFailAlloc_4327_;
                    state = 110;
                    continue;
                }
            }
            110 => {
                return v___x_4326_;
            }
            111 => {
                if v_isShared_4333_ == 0 {
                    v___x_4335_ = v___x_4332_;
                    state = 112;
                    continue;
                } else {
                    v_reuseFailAlloc_4336_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
                    v___x_4335_ = v_reuseFailAlloc_4336_;
                    state = 112;
                    continue;
                }
            }
            112 => {
                return v___x_4335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed(
    mut v_e_4338_: *mut leanh::LeanObject,
    mut v_a_4339_: *mut leanh::LeanObject,
    mut v_a_4340_: *mut leanh::LeanObject,
    mut v_a_4341_: *mut leanh::LeanObject,
    mut v_a_4342_: *mut leanh::LeanObject,
    mut v_a_4343_: *mut leanh::LeanObject,
    mut v_a_4344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4345_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_4338_, v_a_4339_, v_a_4340_, v_a_4341_, v_a_4342_, v_a_4343_);
    leanh::lean_dec(v_a_4343_);
    leanh::lean_dec_ref(v_a_4342_);
    leanh::lean_dec(v_a_4341_);
    leanh::lean_dec_ref(v_a_4340_);
    leanh::lean_dec_ref(v_a_4339_);
    return v_res_4345_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(
    mut v_e_4346_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_a_4348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_4349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: u8 = 0;
    let mut v___x_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: u8 = 0;
    let mut v_arg_4354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: u8 = 0;
    let mut v_arg_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: u8 = 0;
    let mut v___x_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: u8 = 0;
    let mut v___x_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: u8 = 0;
    let mut v___x_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: u8 = 0;
    let mut v___x_4369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: u8 = 0;
    let mut v___x_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: u8 = 0;
    let mut v___x_4376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: u8 = 0;
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: u8 = 0;
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: u8 = 0;
    let mut v___x_4383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4384_: u8 = 0;
    let mut v___x_4385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4352_ = l_Lean_Expr_cleanupAnnotations(v_e_4346_);
                v___x_4353_ = l_Lean_Expr_isApp(v___x_4352_);
                if v___x_4353_ == 0 {
                    leanh::lean_dec_ref(v___x_4352_);
                    return v___x_4353_;
                } else {
                    v_arg_4354_ = leanh::lean_ctor_get(v___x_4352_, 1);
                    leanh::lean_inc_ref(v_arg_4354_);
                    v___x_4355_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4352_);
                    v___x_4356_ = l_Lean_Expr_isApp(v___x_4355_);
                    if v___x_4356_ == 0 {
                        leanh::lean_dec_ref(v___x_4355_);
                        leanh::lean_dec_ref(v_arg_4354_);
                        return v___x_4356_;
                    } else {
                        v_arg_4357_ = leanh::lean_ctor_get(v___x_4355_, 1);
                        leanh::lean_inc_ref(v_arg_4357_);
                        v___x_4358_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4355_);
                        v___x_4359_ = l_Lean_Expr_isApp(v___x_4358_);
                        if v___x_4359_ == 0 {
                            leanh::lean_dec_ref(v___x_4358_);
                            leanh::lean_dec_ref(v_arg_4357_);
                            leanh::lean_dec_ref(v_arg_4354_);
                            return v___x_4359_;
                        } else {
                            v___x_4360_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4358_);
                            v___x_4361_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast___closed__1;
                            v___x_4362_ = l_Lean_Expr_isConstOf(v___x_4360_, v___x_4361_);
                            if v___x_4362_ == 0 {
                                v___x_4363_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast___closed__1;
                                v___x_4364_ = l_Lean_Expr_isConstOf(v___x_4360_, v___x_4363_);
                                if v___x_4364_ == 0 {
                                    v___x_4365_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__1;
                                    v___x_4366_ = l_Lean_Expr_isConstOf(v___x_4360_, v___x_4365_);
                                    if v___x_4366_ == 0 {
                                        v___x_4367_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4;
                                        v___x_4368_ =
                                            l_Lean_Expr_isConstOf(v___x_4360_, v___x_4367_);
                                        if v___x_4368_ == 0 {
                                            v___x_4369_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__7;
                                            v___x_4370_ =
                                                l_Lean_Expr_isConstOf(v___x_4360_, v___x_4369_);
                                            if v___x_4370_ == 0 {
                                                v___x_4371_ = l_Lean_Expr_isApp(v___x_4360_);
                                                if v___x_4371_ == 0 {
                                                    leanh::lean_dec_ref(v___x_4360_);
                                                    leanh::lean_dec_ref(v_arg_4357_);
                                                    leanh::lean_dec_ref(v_arg_4354_);
                                                    return v___x_4371_;
                                                } else {
                                                    v___x_4372_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_4360_,
                                                    );
                                                    v___x_4373_ = l_Lean_Expr_isApp(v___x_4372_);
                                                    if v___x_4373_ == 0 {
                                                        leanh::lean_dec_ref(v___x_4372_);
                                                        leanh::lean_dec_ref(v_arg_4357_);
                                                        leanh::lean_dec_ref(v_arg_4354_);
                                                        return v___x_4373_;
                                                    } else {
                                                        v___x_4374_ =
                                                            l_Lean_Expr_appFnCleanup___redArg(
                                                                v___x_4372_,
                                                            );
                                                        v___x_4375_ =
                                                            l_Lean_Expr_isApp(v___x_4374_);
                                                        if v___x_4375_ == 0 {
                                                            leanh::lean_dec_ref(v___x_4374_);
                                                            leanh::lean_dec_ref(v_arg_4357_);
                                                            leanh::lean_dec_ref(v_arg_4354_);
                                                            return v___x_4375_;
                                                        } else {
                                                            v___x_4376_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_4374_,
                                                                );
                                                            v___x_4377_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__10;
                                                            v___x_4378_ = l_Lean_Expr_isConstOf(
                                                                v___x_4376_,
                                                                v___x_4377_,
                                                            );
                                                            if v___x_4378_ == 0 {
                                                                v___x_4379_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__2;
                                                                v___x_4380_ = l_Lean_Expr_isConstOf(
                                                                    v___x_4376_,
                                                                    v___x_4379_,
                                                                );
                                                                if v___x_4380_ == 0 {
                                                                    v___x_4381_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__13;
                                                                    v___x_4382_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_4376_,
                                                                            v___x_4381_,
                                                                        );
                                                                    if v___x_4382_ == 0 {
                                                                        v___x_4383_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__16;
                                                                        v___x_4384_ =
                                                                            l_Lean_Expr_isConstOf(
                                                                                v___x_4376_,
                                                                                v___x_4383_,
                                                                            );
                                                                        if v___x_4384_ == 0 {
                                                                            v___x_4385_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__19;
                                                                            v___x_4386_ = l_Lean_Expr_isConstOf(v___x_4376_, v___x_4385_);
                                                                            leanh::lean_dec_ref(v___x_4376_);
                                                                            if v___x_4386_ == 0 {
                                                                                leanh::lean_dec_ref(v_arg_4357_);
                                                                                leanh::lean_dec_ref(v_arg_4354_);
                                                                                return v___x_4386_;
                                                                            } else {
                                                                                v_a_4348_ =
                                                                                    v_arg_4357_;
                                                                                v_b_4349_ =
                                                                                    v_arg_4354_;
                                                                                state = 1;
                                                                                continue;
                                                                            }
                                                                        } else {
                                                                            leanh::lean_dec_ref(v___x_4376_);
                                                                            v_a_4348_ = v_arg_4357_;
                                                                            v_b_4349_ = v_arg_4354_;
                                                                            state = 1;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        leanh::lean_dec_ref(
                                                                            v___x_4376_,
                                                                        );
                                                                        v_a_4348_ = v_arg_4357_;
                                                                        v_b_4349_ = v_arg_4354_;
                                                                        state = 1;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    leanh::lean_dec_ref(
                                                                        v___x_4376_,
                                                                    );
                                                                    v_a_4348_ = v_arg_4357_;
                                                                    v_b_4349_ = v_arg_4354_;
                                                                    state = 1;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec_ref(
                                                                    v___x_4376_,
                                                                );
                                                                v_a_4348_ = v_arg_4357_;
                                                                v_b_4349_ = v_arg_4354_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                leanh::lean_dec_ref(v___x_4360_);
                                                leanh::lean_dec_ref(v_arg_4357_);
                                                v_e_4346_ = v_arg_4354_;
                                                state = 0;
                                                continue;
                                            }
                                        } else {
                                            leanh::lean_dec_ref(v___x_4360_);
                                            leanh::lean_dec_ref(v_arg_4357_);
                                            v_e_4346_ = v_arg_4354_;
                                            state = 0;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec_ref(v___x_4360_);
                                        leanh::lean_dec_ref(v_arg_4357_);
                                        leanh::lean_dec_ref(v_arg_4354_);
                                        return v___x_4366_;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v___x_4360_);
                                    leanh::lean_dec_ref(v_arg_4357_);
                                    leanh::lean_dec_ref(v_arg_4354_);
                                    return v___x_4364_;
                                }
                            } else {
                                leanh::lean_dec_ref(v___x_4360_);
                                leanh::lean_dec_ref(v_arg_4357_);
                                leanh::lean_dec_ref(v_arg_4354_);
                                return v___x_4362_;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_4350_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_a_4348_);
                if v___x_4350_ == 0 {
                    leanh::lean_dec_ref(v_b_4349_);
                    return v___x_4350_;
                } else {
                    v_e_4346_ = v_b_4349_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable___boxed(
    mut v_e_4389_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4390_: u8 = 0;
    let mut v_r_4391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4390_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_4389_);
    v_r_4391_ = leanh::lean_box((v_res_4390_) as usize);
    return v_r_4391_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(
    mut v_e_4392_: *mut leanh::LeanObject,
    mut v_type_4393_: *mut leanh::LeanObject,
    mut v_a_4394_: *mut leanh::LeanObject,
    mut v_a_4395_: *mut leanh::LeanObject,
    mut v_a_4396_: *mut leanh::LeanObject,
    mut v_a_4397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4399_: u8 = 0;
    leanh::lean_inc_ref(v_e_4392_);
    v___x_4399_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_4392_);
    if v___x_4399_ == 0 {
        let mut v___x_4400_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_type_4393_);
        leanh::lean_dec_ref(v_e_4392_);
        v___x_4400_ = leanh::lean_box(0);
        v___x_4401_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4401_, 0, v___x_4400_);
        return v___x_4401_;
    } else {
        let mut v___x_4402_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4403_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4402_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___boxed as *mut core::ffi::c_void, 7, 1);
        leanh::lean_closure_set(v___x_4402_, 0, v_e_4392_);
        v___x_4403_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_4393_, v___x_4402_, v_a_4394_, v_a_4395_, v_a_4396_, v_a_4397_);
        return v___x_4403_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f___boxed(
    mut v_e_4404_: *mut leanh::LeanObject,
    mut v_type_4405_: *mut leanh::LeanObject,
    mut v_a_4406_: *mut leanh::LeanObject,
    mut v_a_4407_: *mut leanh::LeanObject,
    mut v_a_4408_: *mut leanh::LeanObject,
    mut v_a_4409_: *mut leanh::LeanObject,
    mut v_a_4410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4411_ = l_Lean_Meta_Grind_Arith_evalFieldExpr_x3f(
        v_e_4404_,
        v_type_4405_,
        v_a_4406_,
        v_a_4407_,
        v_a_4408_,
        v_a_4409_,
    );
    leanh::lean_dec(v_a_4409_);
    leanh::lean_dec_ref(v_a_4408_);
    leanh::lean_dec(v_a_4407_);
    leanh::lean_dec_ref(v_a_4406_);
    return v_res_4411_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4412_ = leanh::lean_unsigned_to_nat(1);
    v___x_4413_ = lean_nat_to_int(v___x_4412_);
    return v___x_4413_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(
    mut v_e_4435_: *mut leanh::LeanObject,
    mut v___y_4436_: *mut leanh::LeanObject,
    mut v___y_4437_: *mut leanh::LeanObject,
    mut v___y_4438_: *mut leanh::LeanObject,
    mut v___y_4439_: *mut leanh::LeanObject,
    mut v___y_4440_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4456_: u8 = 0;
    let mut v_num_4457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_den_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4461_: u8 = 0;
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: u8 = 0;
    let mut v___x_4464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: u8 = 0;
    let mut v___x_4466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v_u_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_4487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4511_: u8 = 0;
    let mut v___x_4512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4530_: u8 = 0;
    let mut v_a_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4534_: u8 = 0;
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_a_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4542_: u8 = 0;
    let mut v___x_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4546_: u8 = 0;
    let mut v_isSharedCheck_4547_: u8 = 0;
    let mut v_a_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4551_: u8 = 0;
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4555_: u8 = 0;
    let mut v_a_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4559_: u8 = 0;
    let mut v___x_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4563_: u8 = 0;
    let mut v___x_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4569_: u8 = 0;
    let mut v___x_4570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4577_: u8 = 0;
    let mut v_u_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4609_: u8 = 0;
    let mut v_a_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4613_: u8 = 0;
    let mut v___x_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4617_: u8 = 0;
    let mut v_isSharedCheck_4618_: u8 = 0;
    let mut v_a_4619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4622_: u8 = 0;
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v___x_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4631_: u8 = 0;
    let mut v_val_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4635_: u8 = 0;
    let mut v_u_4636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: u8 = 0;
    let mut v___x_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4680_: u8 = 0;
    let mut v_isSharedCheck_4681_: u8 = 0;
    let mut v_a_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4685_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4689_: u8 = 0;
    let mut v_isSharedCheck_4690_: u8 = 0;
    let mut v_isSharedCheck_4691_: u8 = 0;
    let mut v_isSharedCheck_4692_: u8 = 0;
    let mut v_a_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4696_: u8 = 0;
    let mut v___x_4698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4700_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_4435_);
                v___x_4442_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval(v_e_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
                if leanh::lean_obj_tag(v___x_4442_) == 0 {
                    v_a_4443_ = leanh::lean_ctor_get(v___x_4442_, 0);
                    v_isSharedCheck_4692_ = (!leanh::lean_is_exclusive(v___x_4442_)) as u8;
                    if v_isSharedCheck_4692_ == 0 {
                        v___x_4445_ = v___x_4442_;
                        v_isShared_4446_ = v_isSharedCheck_4692_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4443_);
                        leanh::lean_dec(v___x_4442_);
                        v___x_4445_ = leanh::lean_box(0);
                        v_isShared_4446_ = v_isSharedCheck_4692_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_4435_);
                    v_a_4693_ = leanh::lean_ctor_get(v___x_4442_, 0);
                    v_isSharedCheck_4700_ = (!leanh::lean_is_exclusive(v___x_4442_)) as u8;
                    if v_isSharedCheck_4700_ == 0 {
                        v___x_4695_ = v___x_4442_;
                        v_isShared_4696_ = v_isSharedCheck_4700_;
                        state = 42;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4693_);
                        leanh::lean_dec(v___x_4442_);
                        v___x_4695_ = leanh::lean_box(0);
                        v_isShared_4696_ = v_isSharedCheck_4700_;
                        state = 42;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4443_) == 0 {
                    leanh::lean_dec_ref(v_e_4435_);
                    v___x_4447_ = leanh::lean_box(0);
                    if v_isShared_4446_ == 0 {
                        leanh::lean_ctor_set(v___x_4445_, 0, v___x_4447_);
                        v___x_4449_ = v___x_4445_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
                        v___x_4449_ = v_reuseFailAlloc_4450_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4445_);
                    v_val_4451_ = leanh::lean_ctor_get(v_a_4443_, 0);
                    leanh::lean_inc(v_val_4451_);
                    leanh::lean_dec_ref_known(v_a_4443_, 1);
                    v_fst_4452_ = leanh::lean_ctor_get(v_val_4451_, 0);
                    v_snd_4453_ = leanh::lean_ctor_get(v_val_4451_, 1);
                    v_isSharedCheck_4691_ = (!leanh::lean_is_exclusive(v_val_4451_)) as u8;
                    if v_isSharedCheck_4691_ == 0 {
                        v___x_4455_ = v_val_4451_;
                        v_isShared_4456_ = v_isSharedCheck_4691_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4453_);
                        leanh::lean_inc(v_fst_4452_);
                        leanh::lean_dec(v_val_4451_);
                        v___x_4455_ = leanh::lean_box(0);
                        v_isShared_4456_ = v_isSharedCheck_4691_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4449_;
            }
            3 => {
                v_num_4457_ = leanh::lean_ctor_get(v_fst_4452_, 0);
                v_den_4458_ = leanh::lean_ctor_get(v_fst_4452_, 1);
                v_isSharedCheck_4690_ = (!leanh::lean_is_exclusive(v_fst_4452_)) as u8;
                if v_isSharedCheck_4690_ == 0 {
                    v___x_4460_ = v_fst_4452_;
                    v_isShared_4461_ = v_isSharedCheck_4690_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_den_4458_);
                    leanh::lean_inc(v_num_4457_);
                    leanh::lean_dec(v_fst_4452_);
                    v___x_4460_ = leanh::lean_box(0);
                    v_isShared_4461_ = v_isSharedCheck_4690_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4462_ = leanh::lean_unsigned_to_nat(1);
                v___x_4463_ = lean_nat_dec_eq(v_den_4458_, v___x_4462_);
                if v___x_4463_ == 0 {
                    v___x_4464_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__0,
                    );
                    v___x_4465_ = lean_int_dec_eq(v_num_4457_, v___x_4464_);
                    if v___x_4465_ == 0 {
                        v___x_4466_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_4457_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
                        if leanh::lean_obj_tag(v___x_4466_) == 0 {
                            v_a_4467_ = leanh::lean_ctor_get(v___x_4466_, 0);
                            leanh::lean_inc(v_a_4467_);
                            leanh::lean_dec_ref_known(v___x_4466_, 1);
                            v_val_4468_ = leanh::lean_ctor_get(v_a_4467_, 0);
                            leanh::lean_inc(v_val_4468_);
                            leanh::lean_dec(v_a_4467_);
                            leanh::lean_inc(v_den_4458_);
                            v___x_4469_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_4458_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
                            if leanh::lean_obj_tag(v___x_4469_) == 0 {
                                v_a_4470_ = leanh::lean_ctor_get(v___x_4469_, 0);
                                leanh::lean_inc(v_a_4470_);
                                leanh::lean_dec_ref_known(v___x_4469_, 1);
                                v_val_4471_ = leanh::lean_ctor_get(v_a_4470_, 0);
                                v_isSharedCheck_4547_ =
                                    (!leanh::lean_is_exclusive(v_a_4470_)) as u8;
                                if v_isSharedCheck_4547_ == 0 {
                                    v___x_4473_ = v_a_4470_;
                                    v_isShared_4474_ = v_isSharedCheck_4547_;
                                    state = 5;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_4471_);
                                    leanh::lean_dec(v_a_4470_);
                                    v___x_4473_ = leanh::lean_box(0);
                                    v_isShared_4474_ = v_isSharedCheck_4547_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_4468_);
                                leanh::lean_del_object(v___x_4460_);
                                leanh::lean_dec(v_den_4458_);
                                leanh::lean_dec(v_num_4457_);
                                leanh::lean_del_object(v___x_4455_);
                                leanh::lean_dec(v_snd_4453_);
                                leanh::lean_dec_ref(v_e_4435_);
                                v_a_4548_ = leanh::lean_ctor_get(v___x_4469_, 0);
                                v_isSharedCheck_4555_ =
                                    (!leanh::lean_is_exclusive(v___x_4469_)) as u8;
                                if v_isSharedCheck_4555_ == 0 {
                                    v___x_4550_ = v___x_4469_;
                                    v_isShared_4551_ = v_isSharedCheck_4555_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_4548_);
                                    leanh::lean_dec(v___x_4469_);
                                    v___x_4550_ = leanh::lean_box(0);
                                    v_isShared_4551_ = v_isSharedCheck_4555_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_del_object(v___x_4460_);
                            leanh::lean_dec(v_den_4458_);
                            leanh::lean_dec(v_num_4457_);
                            leanh::lean_del_object(v___x_4455_);
                            leanh::lean_dec(v_snd_4453_);
                            leanh::lean_dec_ref(v_e_4435_);
                            v_a_4556_ = leanh::lean_ctor_get(v___x_4466_, 0);
                            v_isSharedCheck_4563_ =
                                (!leanh::lean_is_exclusive(v___x_4466_)) as u8;
                            if v_isSharedCheck_4563_ == 0 {
                                v___x_4558_ = v___x_4466_;
                                v_isShared_4559_ = v_isSharedCheck_4563_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4556_);
                                leanh::lean_dec(v___x_4466_);
                                v___x_4558_ = leanh::lean_box(0);
                                v_isShared_4559_ = v_isSharedCheck_4563_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_inc(v_den_4458_);
                        v___x_4564_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkNatCast(v_den_4458_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
                        if leanh::lean_obj_tag(v___x_4564_) == 0 {
                            v_a_4565_ = leanh::lean_ctor_get(v___x_4564_, 0);
                            leanh::lean_inc(v_a_4565_);
                            leanh::lean_dec_ref_known(v___x_4564_, 1);
                            v_val_4566_ = leanh::lean_ctor_get(v_a_4565_, 0);
                            v_isSharedCheck_4618_ =
                                (!leanh::lean_is_exclusive(v_a_4565_)) as u8;
                            if v_isSharedCheck_4618_ == 0 {
                                v___x_4568_ = v_a_4565_;
                                v_isShared_4569_ = v_isSharedCheck_4618_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_4566_);
                                leanh::lean_dec(v_a_4565_);
                                v___x_4568_ = leanh::lean_box(0);
                                v_isShared_4569_ = v_isSharedCheck_4618_;
                                state = 21;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_4460_);
                            leanh::lean_dec(v_den_4458_);
                            leanh::lean_dec(v_num_4457_);
                            leanh::lean_del_object(v___x_4455_);
                            leanh::lean_dec(v_snd_4453_);
                            leanh::lean_dec_ref(v_e_4435_);
                            v_a_4619_ = leanh::lean_ctor_get(v___x_4564_, 0);
                            v_isSharedCheck_4626_ =
                                (!leanh::lean_is_exclusive(v___x_4564_)) as u8;
                            if v_isSharedCheck_4626_ == 0 {
                                v___x_4621_ = v___x_4564_;
                                v_isShared_4622_ = v_isSharedCheck_4626_;
                                state = 30;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4619_);
                                leanh::lean_dec(v___x_4564_);
                                v___x_4621_ = leanh::lean_box(0);
                                v_isShared_4622_ = v_isSharedCheck_4626_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                } else {
                    v___x_4627_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkIntCast(v_num_4457_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
                    if leanh::lean_obj_tag(v___x_4627_) == 0 {
                        v_a_4628_ = leanh::lean_ctor_get(v___x_4627_, 0);
                        v_isSharedCheck_4681_ =
                            (!leanh::lean_is_exclusive(v___x_4627_)) as u8;
                        if v_isSharedCheck_4681_ == 0 {
                            v___x_4630_ = v___x_4627_;
                            v_isShared_4631_ = v_isSharedCheck_4681_;
                            state = 32;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4628_);
                            leanh::lean_dec(v___x_4627_);
                            v___x_4630_ = leanh::lean_box(0);
                            v_isShared_4631_ = v_isSharedCheck_4681_;
                            state = 32;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4460_);
                        leanh::lean_dec(v_den_4458_);
                        leanh::lean_dec(v_num_4457_);
                        leanh::lean_del_object(v___x_4455_);
                        leanh::lean_dec(v_snd_4453_);
                        leanh::lean_dec_ref(v_e_4435_);
                        v_a_4682_ = leanh::lean_ctor_get(v___x_4627_, 0);
                        v_isSharedCheck_4689_ =
                            (!leanh::lean_is_exclusive(v___x_4627_)) as u8;
                        if v_isSharedCheck_4689_ == 0 {
                            v___x_4684_ = v___x_4627_;
                            v_isShared_4685_ = v_isSharedCheck_4689_;
                            state = 40;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4682_);
                            leanh::lean_dec(v___x_4627_);
                            v___x_4684_ = leanh::lean_box(0);
                            v_isShared_4685_ = v_isSharedCheck_4689_;
                            state = 40;
                            continue;
                        }
                    }
                }
            }
            5 => {
                v___x_4475_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4;
                v___x_4476_ = lean_mk_empty_array_with_capacity(v___x_4462_);
                v___x_4477_ = lean_array_push(v___x_4476_, v_val_4471_);
                v___x_4478_ = l_Lean_Meta_mkAppM(
                    v___x_4475_,
                    v___x_4477_,
                    v___y_4437_,
                    v___y_4438_,
                    v___y_4439_,
                    v___y_4440_,
                );
                if leanh::lean_obj_tag(v___x_4478_) == 0 {
                    v_a_4479_ = leanh::lean_ctor_get(v___x_4478_, 0);
                    leanh::lean_inc(v_a_4479_);
                    leanh::lean_dec_ref_known(v___x_4478_, 1);
                    v___x_4480_ = l_Lean_Meta_mkMul(
                        v_val_4468_,
                        v_a_4479_,
                        v___y_4437_,
                        v___y_4438_,
                        v___y_4439_,
                        v___y_4440_,
                    );
                    if leanh::lean_obj_tag(v___x_4480_) == 0 {
                        v_a_4481_ = leanh::lean_ctor_get(v___x_4480_, 0);
                        v_isSharedCheck_4530_ =
                            (!leanh::lean_is_exclusive(v___x_4480_)) as u8;
                        if v_isSharedCheck_4530_ == 0 {
                            v___x_4483_ = v___x_4480_;
                            v_isShared_4484_ = v_isSharedCheck_4530_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4481_);
                            leanh::lean_dec(v___x_4480_);
                            v___x_4483_ = leanh::lean_box(0);
                            v_isShared_4484_ = v_isSharedCheck_4530_;
                            state = 6;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_4473_);
                        leanh::lean_del_object(v___x_4460_);
                        leanh::lean_dec(v_den_4458_);
                        leanh::lean_dec(v_num_4457_);
                        leanh::lean_del_object(v___x_4455_);
                        leanh::lean_dec(v_snd_4453_);
                        leanh::lean_dec_ref(v_e_4435_);
                        v_a_4531_ = leanh::lean_ctor_get(v___x_4480_, 0);
                        v_isSharedCheck_4538_ =
                            (!leanh::lean_is_exclusive(v___x_4480_)) as u8;
                        if v_isSharedCheck_4538_ == 0 {
                            v___x_4533_ = v___x_4480_;
                            v_isShared_4534_ = v_isSharedCheck_4538_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4531_);
                            leanh::lean_dec(v___x_4480_);
                            v___x_4533_ = leanh::lean_box(0);
                            v_isShared_4534_ = v_isSharedCheck_4538_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4473_);
                    leanh::lean_dec(v_val_4468_);
                    leanh::lean_del_object(v___x_4460_);
                    leanh::lean_dec(v_den_4458_);
                    leanh::lean_dec(v_num_4457_);
                    leanh::lean_del_object(v___x_4455_);
                    leanh::lean_dec(v_snd_4453_);
                    leanh::lean_dec_ref(v_e_4435_);
                    v_a_4539_ = leanh::lean_ctor_get(v___x_4478_, 0);
                    v_isSharedCheck_4546_ = (!leanh::lean_is_exclusive(v___x_4478_)) as u8;
                    if v_isSharedCheck_4546_ == 0 {
                        v___x_4541_ = v___x_4478_;
                        v_isShared_4542_ = v_isSharedCheck_4546_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4539_);
                        leanh::lean_dec(v___x_4478_);
                        v___x_4541_ = leanh::lean_box(0);
                        v_isShared_4542_ = v_isSharedCheck_4546_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_u_4485_ = leanh::lean_ctor_get(v___y_4436_, 0);
                v_type_4486_ = leanh::lean_ctor_get(v___y_4436_, 1);
                v_fieldInst_4487_ = leanh::lean_ctor_get(v___y_4436_, 2);
                v___x_4488_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__2;
                v___x_4489_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_4485_);
                if v_isShared_4461_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4460_, 1);
                    leanh::lean_ctor_set(v___x_4460_, 1, v___x_4489_);
                    leanh::lean_ctor_set(v___x_4460_, 0, v_u_4485_);
                    v___x_4491_ = v___x_4460_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4529_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 0, v_u_4485_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4529_, 1, v___x_4489_);
                    v___x_4491_ = v_reuseFailAlloc_4529_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4492_ = l_Lean_mkConst(v___x_4488_, v___x_4491_);
                if v___x_4463_ == 0 {
                    v___x_4521_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_4522_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_4523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_4524_ = l_Lean_instToExprRat_mkInt(v_num_4457_);
                    leanh::lean_inc(v_den_4458_);
                    v___x_4525_ = lean_nat_to_int(v_den_4458_);
                    v___x_4526_ = l_Lean_instToExprRat_mkInt(v___x_4525_);
                    leanh::lean_dec(v___x_4525_);
                    v___x_4527_ = l_Lean_mkApp6(
                        v___x_4521_,
                        v___x_4522_,
                        v___x_4522_,
                        v___x_4522_,
                        v___x_4523_,
                        v___x_4524_,
                        v___x_4526_,
                    );
                    v___y_4509_ = v___x_4527_;
                    state = 12;
                    continue;
                } else {
                    v___x_4528_ = l_Lean_instToExprRat_mkInt(v_num_4457_);
                    v___y_4509_ = v___x_4528_;
                    state = 12;
                    continue;
                }
            }
            8 => {
                v___x_4496_ = l_Lean_mkNatLit(v_den_4458_);
                v___x_4497_ = l_Lean_eagerReflBoolTrue;
                leanh::lean_inc_ref(v_fieldInst_4487_);
                leanh::lean_inc_ref(v_type_4486_);
                v___x_4498_ = l_Lean_mkApp8(
                    v___x_4492_,
                    v_type_4486_,
                    v_fieldInst_4487_,
                    v_e_4435_,
                    v___y_4494_,
                    v___y_4495_,
                    v___x_4496_,
                    v___x_4497_,
                    v_snd_4453_,
                );
                if v_isShared_4456_ == 0 {
                    leanh::lean_ctor_set(v___x_4455_, 1, v___x_4498_);
                    leanh::lean_ctor_set(v___x_4455_, 0, v_a_4481_);
                    v___x_4500_ = v___x_4455_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4507_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4481_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4507_, 1, v___x_4498_);
                    v___x_4500_ = v_reuseFailAlloc_4507_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_4474_ == 0 {
                    leanh::lean_ctor_set(v___x_4473_, 0, v___x_4500_);
                    v___x_4502_ = v___x_4473_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4506_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4506_, 0, v___x_4500_);
                    v___x_4502_ = v_reuseFailAlloc_4506_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_4484_ == 0 {
                    leanh::lean_ctor_set(v___x_4483_, 0, v___x_4502_);
                    v___x_4504_ = v___x_4483_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4505_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
                    v___x_4504_ = v_reuseFailAlloc_4505_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4504_;
            }
            12 => {
                v___x_4510_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
                v___x_4511_ = lean_int_dec_le(v___x_4510_, v_num_4457_);
                if v___x_4511_ == 0 {
                    v___x_4512_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
                    v___x_4513_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
                    v___x_4514_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
                    v___x_4515_ = lean_int_neg(v_num_4457_);
                    leanh::lean_dec(v_num_4457_);
                    v___x_4516_ = l_Int_toNat(v___x_4515_);
                    leanh::lean_dec(v___x_4515_);
                    v___x_4517_ = l_Lean_instToExprInt_mkNat(v___x_4516_);
                    v___x_4518_ = l_Lean_mkApp3(v___x_4512_, v___x_4513_, v___x_4514_, v___x_4517_);
                    v___y_4494_ = v___y_4509_;
                    v___y_4495_ = v___x_4518_;
                    state = 8;
                    continue;
                } else {
                    v___x_4519_ = l_Int_toNat(v_num_4457_);
                    leanh::lean_dec(v_num_4457_);
                    v___x_4520_ = l_Lean_instToExprInt_mkNat(v___x_4519_);
                    v___y_4494_ = v___y_4509_;
                    v___y_4495_ = v___x_4520_;
                    state = 8;
                    continue;
                }
            }
            13 => {
                if v_isShared_4534_ == 0 {
                    v___x_4536_ = v___x_4533_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4531_);
                    v___x_4536_ = v_reuseFailAlloc_4537_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4536_;
            }
            15 => {
                if v_isShared_4542_ == 0 {
                    v___x_4544_ = v___x_4541_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4545_, 0, v_a_4539_);
                    v___x_4544_ = v_reuseFailAlloc_4545_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4544_;
            }
            17 => {
                if v_isShared_4551_ == 0 {
                    v___x_4553_ = v___x_4550_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4554_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4554_, 0, v_a_4548_);
                    v___x_4553_ = v_reuseFailAlloc_4554_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4553_;
            }
            19 => {
                if v_isShared_4559_ == 0 {
                    v___x_4561_ = v___x_4558_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4562_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4562_, 0, v_a_4556_);
                    v___x_4561_ = v_reuseFailAlloc_4562_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4561_;
            }
            21 => {
                v___x_4570_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__4;
                v___x_4571_ = lean_mk_empty_array_with_capacity(v___x_4462_);
                v___x_4572_ = lean_array_push(v___x_4571_, v_val_4566_);
                v___x_4573_ = l_Lean_Meta_mkAppM(
                    v___x_4570_,
                    v___x_4572_,
                    v___y_4437_,
                    v___y_4438_,
                    v___y_4439_,
                    v___y_4440_,
                );
                if leanh::lean_obj_tag(v___x_4573_) == 0 {
                    v_a_4574_ = leanh::lean_ctor_get(v___x_4573_, 0);
                    v_isSharedCheck_4609_ = (!leanh::lean_is_exclusive(v___x_4573_)) as u8;
                    if v_isSharedCheck_4609_ == 0 {
                        v___x_4576_ = v___x_4573_;
                        v_isShared_4577_ = v_isSharedCheck_4609_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4574_);
                        leanh::lean_dec(v___x_4573_);
                        v___x_4576_ = leanh::lean_box(0);
                        v_isShared_4577_ = v_isSharedCheck_4609_;
                        state = 22;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4568_);
                    leanh::lean_del_object(v___x_4460_);
                    leanh::lean_dec(v_den_4458_);
                    leanh::lean_dec(v_num_4457_);
                    leanh::lean_del_object(v___x_4455_);
                    leanh::lean_dec(v_snd_4453_);
                    leanh::lean_dec_ref(v_e_4435_);
                    v_a_4610_ = leanh::lean_ctor_get(v___x_4573_, 0);
                    v_isSharedCheck_4617_ = (!leanh::lean_is_exclusive(v___x_4573_)) as u8;
                    if v_isSharedCheck_4617_ == 0 {
                        v___x_4612_ = v___x_4573_;
                        v_isShared_4613_ = v_isSharedCheck_4617_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4610_);
                        leanh::lean_dec(v___x_4573_);
                        v___x_4612_ = leanh::lean_box(0);
                        v_isShared_4613_ = v_isSharedCheck_4617_;
                        state = 28;
                        continue;
                    }
                }
            }
            22 => {
                v_u_4578_ = leanh::lean_ctor_get(v___y_4436_, 0);
                v_type_4579_ = leanh::lean_ctor_get(v___y_4436_, 1);
                v_fieldInst_4580_ = leanh::lean_ctor_get(v___y_4436_, 2);
                v___x_4581_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__4;
                v___x_4582_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_4578_);
                if v_isShared_4461_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4460_, 1);
                    leanh::lean_ctor_set(v___x_4460_, 1, v___x_4582_);
                    leanh::lean_ctor_set(v___x_4460_, 0, v_u_4578_);
                    v___x_4584_ = v___x_4460_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_4608_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_u_4578_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4608_, 1, v___x_4582_);
                    v___x_4584_ = v_reuseFailAlloc_4608_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_4585_ = l_Lean_mkConst(v___x_4581_, v___x_4584_);
                if v___x_4463_ == 0 {
                    v___x_4600_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_4601_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_4602_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_4603_ = l_Lean_instToExprRat_mkInt(v_num_4457_);
                    leanh::lean_dec(v_num_4457_);
                    leanh::lean_inc(v_den_4458_);
                    v___x_4604_ = lean_nat_to_int(v_den_4458_);
                    v___x_4605_ = l_Lean_instToExprRat_mkInt(v___x_4604_);
                    leanh::lean_dec(v___x_4604_);
                    v___x_4606_ = l_Lean_mkApp6(
                        v___x_4600_,
                        v___x_4601_,
                        v___x_4601_,
                        v___x_4601_,
                        v___x_4602_,
                        v___x_4603_,
                        v___x_4605_,
                    );
                    v___y_4587_ = v___x_4606_;
                    state = 24;
                    continue;
                } else {
                    v___x_4607_ = l_Lean_instToExprRat_mkInt(v_num_4457_);
                    leanh::lean_dec(v_num_4457_);
                    v___y_4587_ = v___x_4607_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_4588_ = l_Lean_mkNatLit(v_den_4458_);
                v___x_4589_ = l_Lean_eagerReflBoolTrue;
                leanh::lean_inc_ref(v_fieldInst_4580_);
                leanh::lean_inc_ref(v_type_4579_);
                v___x_4590_ = l_Lean_mkApp7(
                    v___x_4585_,
                    v_type_4579_,
                    v_fieldInst_4580_,
                    v_e_4435_,
                    v___y_4587_,
                    v___x_4588_,
                    v___x_4589_,
                    v_snd_4453_,
                );
                if v_isShared_4456_ == 0 {
                    leanh::lean_ctor_set(v___x_4455_, 1, v___x_4590_);
                    leanh::lean_ctor_set(v___x_4455_, 0, v_a_4574_);
                    v___x_4592_ = v___x_4455_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_4599_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_a_4574_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4599_, 1, v___x_4590_);
                    v___x_4592_ = v_reuseFailAlloc_4599_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_4569_ == 0 {
                    leanh::lean_ctor_set(v___x_4568_, 0, v___x_4592_);
                    v___x_4594_ = v___x_4568_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4598_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4598_, 0, v___x_4592_);
                    v___x_4594_ = v_reuseFailAlloc_4598_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_4577_ == 0 {
                    leanh::lean_ctor_set(v___x_4576_, 0, v___x_4594_);
                    v___x_4596_ = v___x_4576_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_4597_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4597_, 0, v___x_4594_);
                    v___x_4596_ = v_reuseFailAlloc_4597_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_4596_;
            }
            28 => {
                if v_isShared_4613_ == 0 {
                    v___x_4615_ = v___x_4612_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_4616_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4616_, 0, v_a_4610_);
                    v___x_4615_ = v_reuseFailAlloc_4616_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_4615_;
            }
            30 => {
                if v_isShared_4622_ == 0 {
                    v___x_4624_ = v___x_4621_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4624_;
            }
            32 => {
                v_val_4632_ = leanh::lean_ctor_get(v_a_4628_, 0);
                v_isSharedCheck_4680_ = (!leanh::lean_is_exclusive(v_a_4628_)) as u8;
                if v_isSharedCheck_4680_ == 0 {
                    v___x_4634_ = v_a_4628_;
                    v_isShared_4635_ = v_isSharedCheck_4680_;
                    state = 33;
                    continue;
                } else {
                    leanh::lean_inc(v_val_4632_);
                    leanh::lean_dec(v_a_4628_);
                    v___x_4634_ = leanh::lean_box(0);
                    v_isShared_4635_ = v_isSharedCheck_4680_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v_u_4636_ = leanh::lean_ctor_get(v___y_4436_, 0);
                v_type_4637_ = leanh::lean_ctor_get(v___y_4436_, 1);
                v_fieldInst_4638_ = leanh::lean_ctor_get(v___y_4436_, 2);
                v___x_4639_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___closed__6;
                v___x_4640_ = leanh::lean_box(0);
                leanh::lean_inc(v_u_4636_);
                if v_isShared_4461_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4460_, 1);
                    leanh::lean_ctor_set(v___x_4460_, 1, v___x_4640_);
                    leanh::lean_ctor_set(v___x_4460_, 0, v_u_4636_);
                    v___x_4642_ = v___x_4460_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4679_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_u_4636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4679_, 1, v___x_4640_);
                    v___x_4642_ = v_reuseFailAlloc_4679_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                v___x_4643_ = l_Lean_mkConst(v___x_4639_, v___x_4642_);
                if v___x_4463_ == 0 {
                    v___x_4671_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__7);
                    v___x_4672_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__10);
                    v___x_4673_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_mkBin___redArg___closed__15);
                    v___x_4674_ = l_Lean_instToExprRat_mkInt(v_num_4457_);
                    v___x_4675_ = lean_nat_to_int(v_den_4458_);
                    v___x_4676_ = l_Lean_instToExprRat_mkInt(v___x_4675_);
                    leanh::lean_dec(v___x_4675_);
                    v___x_4677_ = l_Lean_mkApp6(
                        v___x_4671_,
                        v___x_4672_,
                        v___x_4672_,
                        v___x_4672_,
                        v___x_4673_,
                        v___x_4674_,
                        v___x_4676_,
                    );
                    v___y_4659_ = v___x_4677_;
                    state = 39;
                    continue;
                } else {
                    leanh::lean_dec(v_den_4458_);
                    v___x_4678_ = l_Lean_instToExprRat_mkInt(v_num_4457_);
                    v___y_4659_ = v___x_4678_;
                    state = 39;
                    continue;
                }
            }
            35 => {
                v___x_4647_ = l_Lean_eagerReflBoolTrue;
                leanh::lean_inc_ref(v_fieldInst_4638_);
                leanh::lean_inc_ref(v_type_4637_);
                v___x_4648_ = l_Lean_mkApp7(
                    v___x_4643_,
                    v_type_4637_,
                    v_fieldInst_4638_,
                    v_e_4435_,
                    v___y_4645_,
                    v___y_4646_,
                    v___x_4647_,
                    v_snd_4453_,
                );
                if v_isShared_4456_ == 0 {
                    leanh::lean_ctor_set(v___x_4455_, 1, v___x_4648_);
                    leanh::lean_ctor_set(v___x_4455_, 0, v_val_4632_);
                    v___x_4650_ = v___x_4455_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_4657_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_val_4632_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 1, v___x_4648_);
                    v___x_4650_ = v_reuseFailAlloc_4657_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_4635_ == 0 {
                    leanh::lean_ctor_set(v___x_4634_, 0, v___x_4650_);
                    v___x_4652_ = v___x_4634_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4656_, 0, v___x_4650_);
                    v___x_4652_ = v_reuseFailAlloc_4656_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                if v_isShared_4631_ == 0 {
                    leanh::lean_ctor_set(v___x_4630_, 0, v___x_4652_);
                    v___x_4654_ = v___x_4630_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_4655_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4655_, 0, v___x_4652_);
                    v___x_4654_ = v_reuseFailAlloc_4655_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_4654_;
            }
            39 => {
                v___x_4660_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__35);
                v___x_4661_ = lean_int_dec_le(v___x_4660_, v_num_4457_);
                if v___x_4661_ == 0 {
                    v___x_4662_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__36);
                    v___x_4663_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__39);
                    v___x_4664_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_eval___closed__42);
                    v___x_4665_ = lean_int_neg(v_num_4457_);
                    leanh::lean_dec(v_num_4457_);
                    v___x_4666_ = l_Int_toNat(v___x_4665_);
                    leanh::lean_dec(v___x_4665_);
                    v___x_4667_ = l_Lean_instToExprInt_mkNat(v___x_4666_);
                    v___x_4668_ = l_Lean_mkApp3(v___x_4662_, v___x_4663_, v___x_4664_, v___x_4667_);
                    v___y_4645_ = v___y_4659_;
                    v___y_4646_ = v___x_4668_;
                    state = 35;
                    continue;
                } else {
                    v___x_4669_ = l_Int_toNat(v_num_4457_);
                    leanh::lean_dec(v_num_4457_);
                    v___x_4670_ = l_Lean_instToExprInt_mkNat(v___x_4669_);
                    v___y_4645_ = v___y_4659_;
                    v___y_4646_ = v___x_4670_;
                    state = 35;
                    continue;
                }
            }
            40 => {
                if v_isShared_4685_ == 0 {
                    v___x_4687_ = v___x_4684_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
                    v___x_4687_ = v_reuseFailAlloc_4688_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4687_;
            }
            42 => {
                if v_isShared_4696_ == 0 {
                    v___x_4698_ = v___x_4695_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4699_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4699_, 0, v_a_4693_);
                    v___x_4698_ = v_reuseFailAlloc_4699_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed(
    mut v_e_4701_: *mut leanh::LeanObject,
    mut v___y_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
    mut v___y_4704_: *mut leanh::LeanObject,
    mut v___y_4705_: *mut leanh::LeanObject,
    mut v___y_4706_: *mut leanh::LeanObject,
    mut v___y_4707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4708_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0(
        v_e_4701_,
        v___y_4702_,
        v___y_4703_,
        v___y_4704_,
        v___y_4705_,
        v___y_4706_,
    );
    leanh::lean_dec(v___y_4706_);
    leanh::lean_dec_ref(v___y_4705_);
    leanh::lean_dec(v___y_4704_);
    leanh::lean_dec_ref(v___y_4703_);
    leanh::lean_dec_ref(v___y_4702_);
    return v_res_4708_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(
    mut v_e_4709_: *mut leanh::LeanObject,
    mut v_type_4710_: *mut leanh::LeanObject,
    mut v_a_4711_: *mut leanh::LeanObject,
    mut v_a_4712_: *mut leanh::LeanObject,
    mut v_a_4713_: *mut leanh::LeanObject,
    mut v_a_4714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4716_: u8 = 0;
    leanh::lean_inc_ref(v_e_4709_);
    v___x_4716_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_isApplicable(v_e_4709_);
    if v___x_4716_ == 0 {
        let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_type_4710_);
        leanh::lean_dec_ref(v_e_4709_);
        v___x_4717_ = leanh::lean_box(0);
        v___x_4718_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_4718_, 0, v___x_4717_);
        return v___x_4718_;
    } else {
        let mut v___f_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4720_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___f_4719_ = leanh::lean_alloc_closure(
            l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___lam__0___boxed as *mut core::ffi::c_void,
            7,
            1,
        );
        leanh::lean_closure_set(v___f_4719_, 0, v_e_4709_);
        v___x_4720_ = l___private_Lean_Meta_Tactic_Grind_Arith_FieldNormNum_0__Lean_Meta_Grind_Arith_FieldNormNum_run_x3f___redArg(v_type_4710_, v___f_4719_, v_a_4711_, v_a_4712_, v_a_4713_, v_a_4714_);
        return v___x_4720_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_normFieldExpr_x3f___boxed(
    mut v_e_4721_: *mut leanh::LeanObject,
    mut v_type_4722_: *mut leanh::LeanObject,
    mut v_a_4723_: *mut leanh::LeanObject,
    mut v_a_4724_: *mut leanh::LeanObject,
    mut v_a_4725_: *mut leanh::LeanObject,
    mut v_a_4726_: *mut leanh::LeanObject,
    mut v_a_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4728_ = l_Lean_Meta_Grind_Arith_normFieldExpr_x3f(
        v_e_4721_,
        v_type_4722_,
        v_a_4723_,
        v_a_4724_,
        v_a_4725_,
        v_a_4726_,
    );
    leanh::lean_dec(v_a_4726_);
    leanh::lean_dec_ref(v_a_4725_);
    leanh::lean_dec(v_a_4724_);
    leanh::lean_dec_ref(v_a_4723_);
    return v_res_4728_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_FieldNormNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SafeExponentiation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_FieldNormNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_LitValues(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_SafeExponentiation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_FieldNormNum(builtin);
}