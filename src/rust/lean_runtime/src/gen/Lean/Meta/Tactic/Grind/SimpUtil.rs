// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.SimpUtil
// Imports: Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Grind.MatchDiscrOnly Lean.Meta.Tactic.Grind.ForallProp Lean.Meta.Tactic.Grind.Arith.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs.List Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core Lean.Meta.Tactic.Grind.Util Lean.Meta.Sym.Util Init.Grind.Norm Init.Grind.Config Init.ByCases Lean.Meta.Tactic.Simp.Main
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Grind::Config::{
    initialize_Init_Grind_Config, runtime_initialize_Init_Grind_Config,
};
use crate::r#gen::Init::Grind::Norm::{
    initialize_Init_Grind_Norm, runtime_initialize_Init_Grind_Norm,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4,
};
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_Node_isEmpty___redArg, l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations,
    l_Lean_Expr_constLevels_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Expr_isForall, l_Lean_Expr_isProp,
    l_Lean_mkAnd, l_Lean_mkApp3, l_Lean_mkApp4, l_Lean_mkApp5, l_Lean_mkAppB, l_Lean_mkBVar,
    l_Lean_mkConst, l_Lean_mkForall, l_Lean_mkIntAdd, l_Lean_mkIntLE, l_Lean_mkIntLit,
    l_Lean_mkLambda, l_Lean_mkNatAdd, l_Lean_mkNatLE, l_Lean_mkNatLit, l_Lean_mkNot, l_Lean_mkOr,
};
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqFalse_x27, l_Lean_Meta_mkNoConfusion,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_Meta_Context_config,
    l_Lean_Meta_Context_configKey, l_Lean_Meta_TransparencyMode_toUInt64,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_mkLambdaFVars,
};
use crate::r#gen::Lean::Meta::CtorRecognizer::l_Lean_Meta_isConstructorApp_x3f;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_unfoldReducibleStep,
    runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Simproc::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Simproc, l_Lean_Meta_Grind_Arith_addSimproc,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Attr::l_Lean_Meta_Grind_normExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::ForallProp::{
    initialize_Lean_Meta_Tactic_Grind_ForallProp, l_Lean_Meta_Grind_addForallSimproc,
    runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::MatchDiscrOnly::{
    initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly, l_Lean_Meta_Grind_addSimpMatchDiscrsOnly,
    runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_addPreMatchCondSimproc,
    runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::Core::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::BuiltinSimprocs::List::{
    initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List,
    runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Main::{
    initialize_Lean_Meta_Tactic_Simp_Main, l_Lean_Meta_simp,
    runtime_initialize_Lean_Meta_Tactic_Simp_Main,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpCongrTheorems::l_Lean_Meta_getSimpCongrTheorems___redArg;
use crate::r#gen::Lean::Meta::Tactic::Simp::SimpTheorems::{
    l_Lean_Meta_SimpExtension_getTheorems___redArg, l_Lean_Meta_SimpTheorems_addDeclToUnfold,
    l_Lean_Meta_addSimpTheorem,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Simproc::{
    initialize_Lean_Meta_Tactic_Simp_Simproc, l_Lean_Meta_Simp_Simprocs_add,
    l_Lean_Meta_Simp_Simprocs_erase, l_Lean_Meta_Simp_getSEvalSimprocs___redArg,
    l_Lean_Meta_Simp_registerBuiltinDSimproc, l_Lean_Meta_Simp_registerBuiltinSimproc,
    runtime_initialize_Lean_Meta_Tactic_Simp_Simproc,
};
use crate::r#gen::Lean::Meta::Tactic::Simp::Types::l_Lean_Meta_Simp_mkContext___redArg;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_ctor_set_usize, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_uint64_once, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Grind_registerNormTheorems___closed__0_value: LeanStringObject<61> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 61,
        m_capacity: 61,
        m_length: 60,
        m_data: [
            96, 103, 114, 105, 110, 100, 96, 32, 110, 111, 114, 109, 97, 108, 105, 122, 97, 116,
            105, 111, 110, 32, 116, 104, 101, 111, 114, 101, 109, 115, 32, 104, 97, 118, 101, 32,
            97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 105, 110, 105, 116, 105,
            97, 108, 105, 122, 101, 100, 0,
        ],
    };
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_registerNormTheorems___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_registerNormTheorems___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [66, 111, 111, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__1_value) as *mut LeanObject,1655553077289932752 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [66, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [98, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__3_value) as *mut LeanObject,16093780639914376387 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__4_value) as *mut LeanObject,9753356465987597394 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [68, 101, 99, 105, 100, 97, 98, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [100, 101, 99, 105, 100, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__6_value) as *mut LeanObject,4342836574150310743 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__7_value) as *mut LeanObject,15998082856370921488 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [97, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__9_value) as *mut LeanObject,6148012076188572320 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [111, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__11_value) as *mut LeanObject,13145409667090857818 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 2,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__1_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__1_value)
                as *mut LeanObject,
            16122875713692181903 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__4_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [84, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__4_value)
                as *mut LeanObject,
            11870096045526947150 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__5_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__7_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [70, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__8_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__7_value)
                as *mut LeanObject,
            907667957179513571 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__8_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__9_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__9: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__10_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 101, 97, 110, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__11_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [71, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__12_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [101, 113, 95, 102, 97, 108, 115, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__12_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__13_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__12_value)
                as *mut LeanObject,
            11584624889955424335 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__13_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__15_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [101, 113, 95, 116, 114, 117, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__15_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__15_value)
                as *mut LeanObject,
            6518306046597794916 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__18_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [101, 113, 95, 115, 101, 108, 102, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__18_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__19_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__18_value)
                as *mut LeanObject,
            12181656444938130656 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__19_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__20_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__20_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__21_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__21_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__20_value)
                as *mut LeanObject,
            9255189395584251158 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__21_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__22_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__22: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__23_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            98, 111, 111, 108, 95, 101, 113, 95, 116, 111, 95, 112, 114, 111, 112, 0,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__23: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__23_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__24_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__23_value)
                as *mut LeanObject,
            12040479670535018831 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__24: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__24_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__25_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__25: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__26_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [102, 108, 105, 112, 95, 98, 111, 111, 108, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__26_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__27_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__26_value)
                as *mut LeanObject,
            3966638278125175059 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__27: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__27_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__28: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__29_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__29_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_simpEq___redArg___closed__30_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__30_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__29_value)
                as *mut LeanObject,
            15761733860085307253 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpEq___redArg___closed__30: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__30_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 69, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,8256812394612487643 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__2_value) as *mut LeanObject,((( 3 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value: LeanArrayObject<4> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*4) as u16, other: 0, tag: 246 }, m_size: 4, m_capacity: 4, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [100, 105, 116, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__0_value)
                as *mut LeanObject,
            8391571994004792969 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [105, 116, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__2_value)
                as *mut LeanObject,
            18356704233129443855 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [100, 105, 116, 101, 95, 101, 113, 95, 105, 116, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__4_value)
                as *mut LeanObject,
            14630272000144361786 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpDIte___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 68, 73, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut LeanObject,11972642169564782543 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_simpDIte___redArg___closed__1_value) as *mut LeanObject,((( 5 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value: LeanArrayObject<6> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*6) as u16, other: 0, tag: 246 }, m_size: 6, m_capacity: 6, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 111, 116, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__0_value)
                as *mut LeanObject,
            16612019923665488825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [69, 120, 105, 115, 116, 115, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__2_value)
                as *mut LeanObject,
            5086165725197901121 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__4_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [110, 111, 116, 95, 102, 111, 114, 97, 108, 108, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__4_value)
                as *mut LeanObject,
            1910603056246669445 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__6_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [110, 111, 116, 95, 105, 109, 112, 108, 105, 101, 115, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__6_value)
                as *mut LeanObject,
            4878178320848305550 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__9_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [79, 114, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__9_value)
                as *mut LeanObject,
            14181099489592536354 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__10_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__11_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [65, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__11_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__12_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__11_value)
                as *mut LeanObject,
            9743492140944907313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__12_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__13_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [76, 69, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__13_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__14_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [108, 101, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__14: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__14_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__13_value)
                as *mut LeanObject,
            8347582161988589016 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__15_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__15_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__14_value)
                as *mut LeanObject,
            7316284823769321069 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__15_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__16_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [110, 111, 116, 95, 105, 116, 101, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__16_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__17_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__16_value)
                as *mut LeanObject,
            10012160887734445444 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__17: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__17_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__18_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__18: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__19_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 97, 116, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__20_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__20: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__20_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__21_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [73, 110, 116, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__21: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__22_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__22: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__22_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__23_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__23: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__24_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__24: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__25_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 111, 116, 95, 108, 101, 95, 101, 113, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__25: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__21_value)
                as *mut LeanObject,
            7009148538150066493 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__26_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__26_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
                as *mut LeanObject,
            5162611250653448781 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__26: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__26_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__27_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__27: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__28_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__28: *mut LeanObject = core::ptr::null_mut();
static l_Lean_Meta_Grind_pushNot___redArg___closed__29_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__29_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__29_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__25_value)
                as *mut LeanObject,
            4324381115663783915 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__29: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__29_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__30_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__30: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__31_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__31: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__32_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [110, 111, 116, 95, 101, 113, 95, 116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__32: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__32_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__33_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__33_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__33_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__32_value)
                as *mut LeanObject,
            11675589336077694177 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__33: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__33_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__34_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__34: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__35_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [110, 111, 116, 95, 101, 113, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__35: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__35_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__36_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__36_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__36_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__35_value)
                as *mut LeanObject,
            2183596451816792659 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__36: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__36_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__37_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__37: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__38_value: LeanStringObject<12> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [110, 111, 116, 95, 101, 113, 95, 112, 114, 111, 112, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__38: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__38_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__39_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__38_value)
                as *mut LeanObject,
            14629220074354903389 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__39: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__39_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__40_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__40: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__41_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__41: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__42_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [110, 111, 116, 95, 97, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__42: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__42_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__43_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__42_value)
                as *mut LeanObject,
            1943741726499332591 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__43: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__43_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__44_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__44: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__45_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__45: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__46_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 7,
        m_capacity: 7,
        m_length: 6,
        m_data: [110, 111, 116, 95, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__46: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__46_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__47_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__46_value)
                as *mut LeanObject,
            2778442929519348459 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__47: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__47_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__48_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__48: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__49_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [97, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__49: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__49_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__50_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__49_value)
                as *mut LeanObject,
            7839396180116328695 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__50: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__50_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__51_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__51: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__52_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [110, 111, 116, 95, 101, 120, 105, 115, 116, 115, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__52: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__52_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__53_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__52_value)
                as *mut LeanObject,
            14364261837424776314 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__53: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__53_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__54_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [110, 111, 116, 95, 110, 111, 116, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__54: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__54_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__55_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__54_value)
                as *mut LeanObject,
            1433178546513579301 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__55: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__55_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__56_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__56: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__57_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [110, 111, 116, 95, 116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__57: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__57_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__58_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__57_value)
                as *mut LeanObject,
            13154267707496524221 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__58: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__58_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__59_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__59: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__60_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__60: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__61_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [110, 111, 116, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__61: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__61_value) as *mut LeanObject;
static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_pushNot___redArg___closed__62_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__61_value)
                as *mut LeanObject,
            1591550254088102176 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__62: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__62_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__63_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__63: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__64_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_pushNot___redArg___closed__64: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [112, 117, 115, 104, 78, 111, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut LeanObject,14132401962984515005 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__1_value) as *mut LeanObject,((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value: LeanArrayObject<2> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*2) as u16, other: 0, tag: 246 }, m_size: 2, m_capacity: 2, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10__value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__0_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [111, 114, 95, 115, 119, 97, 112, 49, 51, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__0_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__0_value)
                as *mut LeanObject,
            7325503363791193584 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__1_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__3_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [111, 114, 95, 115, 119, 97, 112, 49, 50, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__3_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__3_value)
                as *mut LeanObject,
            3950801501127104890 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__6_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [111, 114, 95, 116, 114, 117, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__6_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__6_value)
                as *mut LeanObject,
            15885495678138479146 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__7_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__8_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__9_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 114, 95, 102, 97, 108, 115, 101, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__10_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__9_value)
                as *mut LeanObject,
            14011086014131787929 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__10_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__11_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__11: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__12_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [111, 114, 95, 97, 115, 115, 111, 99, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__12_value) as *mut LeanObject;
static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value)
                as *mut LeanObject,
            11948124481539785030 as *mut LeanObject,
        ],
    };
static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value)
                as *mut LeanObject,
            13563742693681136756 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__13_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__12_value)
                as *mut LeanObject,
            8641488168956777649 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__13_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__14_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__14: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__15_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [116, 114, 117, 101, 95, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__15: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__15_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__16_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__15_value)
                as *mut LeanObject,
            3037741586801491095 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__16: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__16_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__17_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__17: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__18_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [102, 97, 108, 115, 101, 95, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__18: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__18_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_simpOr___redArg___closed__19_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__18_value)
                as *mut LeanObject,
            7030941873239652894 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__19: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_simpOr___redArg___closed__19_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__20_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_simpOr___redArg___closed__20: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 105, 109, 112, 79, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut LeanObject,11712137666541898468 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 4 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__10_value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value: LeanArrayObject<3> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*3) as u16, other: 0, tag: 246 }, m_size: 3, m_capacity: 3, m_data: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11__value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0: u64 = 0;
pub static l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value: LeanStringObject<2> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [104, 0],
    };
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__0_value)
                as *mut LeanObject,
            8738205681931236784 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 67, 104, 101, 97, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut LeanObject,7640757303824383266 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed as *const core::ffi::c_void, m_arity: 9, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [117, 110, 102, 111, 108, 100, 82, 101, 100, 117, 99, 105, 98, 108, 101, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__10_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Meta_Grind_simpEq___redArg___closed__11_value) as *mut LeanObject,15218882539576375456 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut LeanObject,18075408319424519475 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value: LeanArrayObject<1> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 246 }, m_size: 1, m_capacity: 1, m_data: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9__value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [76, 105, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value: LeanStringObject<16> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 16,
        m_capacity: 16,
        m_length: 15,
        m_data: [
            114, 101, 100, 117, 99, 101, 82, 101, 112, 108, 105, 99, 97, 116, 101, 0,
        ],
    };
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value)
        as *mut LeanObject;
static l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__0_value)
                as *mut LeanObject,
            9582258842178272501 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__1_value)
                as *mut LeanObject,
            4445492996492257536 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value: LeanStringObject<13> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 13,
        m_capacity: 13,
        m_length: 12,
        m_data: [114, 101, 100, 117, 99, 101, 67, 116, 111, 114, 69, 113, 0],
    };
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__3_value)
                as *mut LeanObject,
            233589347272681201 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getSimprocs___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getSimprocs___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 69, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__1_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 101, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__1_value) as *mut LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__0_value)
                as *mut LeanObject,
            1755019837031360842 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__2_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__2_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__1_value)
                as *mut LeanObject,
            5555145617058846791 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__2_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__3_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [71, 84, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__3_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__4_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [103, 116, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__4_value) as *mut LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__3_value)
                as *mut LeanObject,
            2272833755566510320 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__5_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__5_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__4_value)
                as *mut LeanObject,
            9426339939459091439 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__5_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__6_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [99, 97, 115, 116, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__6_value) as *mut LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_pushNot___redArg___closed__19_value)
                as *mut LeanObject,
            11442535297760353691 as *mut LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__7_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__7_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__6_value)
                as *mut LeanObject,
            8075995802451307795 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__7_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__8_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [120, 111, 114, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__8_value) as *mut LeanObject;
static l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__0_value) as *mut LeanObject,12882480457794858234 as *mut LeanObject] };
pub static l_Lean_Meta_Grind_getNormTheorems___closed__9_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__9_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__8_value)
                as *mut LeanObject,
            10425341760733586335 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__9_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__10_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [78, 101, 0],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__10_value) as *mut LeanObject;
pub static l_Lean_Meta_Grind_getNormTheorems___closed__11_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__10_value)
                as *mut LeanObject,
            6695605208187598753 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_getNormTheorems___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_getNormTheorems___closed__11_value) as *mut LeanObject;
static mut l_Lean_Meta_Grind_normalizeImp___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_normalizeImp___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_normalizeImp___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_normalizeImp___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_normalizeImp___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_normalizeImp___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_normalizeImp___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_normalizeImp___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_normalizeImp___closed__6: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(
    mut v_x_2220_: *mut LeanObject,
) -> u8 {
    let mut v___x_2221_: u8 = 0;
    v___x_2221_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2220_);
    return v___x_2221_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg___boxed(
    mut v_x_2222_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2223_: u8 = 0;
    let mut v_r_2224_: *mut LeanObject = core::ptr::null_mut();
    v_res_2223_ = l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___redArg(v_x_2222_);
    lean_dec_ref(v_x_2222_);
    v_r_2224_ = lean_box((v_res_2223_) as usize);
    return v_r_2224_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(
    mut v_00_u03b2_2225_: *mut LeanObject,
    mut v_x_2226_: *mut LeanObject,
) -> u8 {
    let mut v___x_2227_: u8 = 0;
    v___x_2227_ = l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_x_2226_);
    return v___x_2227_;
}
pub unsafe fn l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2___boxed(
    mut v_00_u03b2_2228_: *mut LeanObject,
    mut v_x_2229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2230_: u8 = 0;
    let mut v_r_2231_: *mut LeanObject = core::ptr::null_mut();
    v_res_2230_ =
        l_Lean_PersistentHashMap_isEmpty___at___00Lean_Meta_Grind_registerNormTheorems_spec__2(
            v_00_u03b2_2228_,
            v_x_2229_,
        );
    lean_dec_ref(v_x_2229_);
    v_r_2231_ = lean_box((v_res_2230_) as usize);
    return v_r_2231_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(
    mut v_msgData_2232_: *mut LeanObject,
    mut v___y_2233_: *mut LeanObject,
    mut v___y_2234_: *mut LeanObject,
    mut v___y_2235_: *mut LeanObject,
    mut v___y_2236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    v___x_2238_ = lean_st_ref_get(v___y_2236_);
    v_env_2239_ = lean_ctor_get(v___x_2238_, 0);
    lean_inc_ref(v_env_2239_);
    lean_dec(v___x_2238_);
    v___x_2240_ = lean_st_ref_get(v___y_2234_);
    v_mctx_2241_ = lean_ctor_get(v___x_2240_, 0);
    lean_inc_ref(v_mctx_2241_);
    lean_dec(v___x_2240_);
    v_lctx_2242_ = lean_ctor_get(v___y_2233_, 2);
    v_options_2243_ = lean_ctor_get(v___y_2235_, 2);
    lean_inc_ref(v_options_2243_);
    lean_inc_ref(v_lctx_2242_);
    v___x_2244_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2244_, 0, v_env_2239_);
    lean_ctor_set(v___x_2244_, 1, v_mctx_2241_);
    lean_ctor_set(v___x_2244_, 2, v_lctx_2242_);
    lean_ctor_set(v___x_2244_, 3, v_options_2243_);
    v___x_2245_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2245_, 0, v___x_2244_);
    lean_ctor_set(v___x_2245_, 1, v_msgData_2232_);
    v___x_2246_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2246_, 0, v___x_2245_);
    return v___x_2246_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3___boxed(
    mut v_msgData_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2253_: *mut LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msgData_2247_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
    lean_dec(v___y_2251_);
    lean_dec_ref(v___y_2250_);
    lean_dec(v___y_2249_);
    lean_dec_ref(v___y_2248_);
    return v_res_2253_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
    mut v_msg_2254_: *mut LeanObject,
    mut v___y_2255_: *mut LeanObject,
    mut v___y_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2260_ = lean_ctor_get(v___y_2257_, 5);
                v___x_2261_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3_spec__3(v_msg_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
                v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
                v_isSharedCheck_2270_ = (!lean_is_exclusive(v___x_2261_)) as u8;
                if v_isSharedCheck_2270_ == 0 {
                    v___x_2264_ = v___x_2261_;
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2262_);
                    lean_dec(v___x_2261_);
                    v___x_2264_ = lean_box(0);
                    v_isShared_2265_ = v_isSharedCheck_2270_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2260_);
                v___x_2266_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2266_, 0, v_ref_2260_);
                lean_ctor_set(v___x_2266_, 1, v_a_2262_);
                if v_isShared_2265_ == 0 {
                    lean_ctor_set_tag(v___x_2264_, 1);
                    lean_ctor_set(v___x_2264_, 0, v___x_2266_);
                    v___x_2268_ = v___x_2264_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2269_, 0, v___x_2266_);
                    v___x_2268_ = v_reuseFailAlloc_2269_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2268_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg___boxed(
    mut v_msg_2271_: *mut LeanObject,
    mut v___y_2272_: *mut LeanObject,
    mut v___y_2273_: *mut LeanObject,
    mut v___y_2274_: *mut LeanObject,
    mut v___y_2275_: *mut LeanObject,
    mut v___y_2276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2277_: *mut LeanObject = core::ptr::null_mut();
    v_res_2277_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
        v_msg_2271_,
        v___y_2272_,
        v___y_2273_,
        v___y_2274_,
        v___y_2275_,
    );
    lean_dec(v___y_2275_);
    lean_dec_ref(v___y_2274_);
    lean_dec(v___y_2273_);
    lean_dec_ref(v___y_2272_);
    return v_res_2277_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(
    mut v_as_2278_: *mut LeanObject,
    mut v_sz_2279_: usize,
    mut v_i_2280_: usize,
    mut v_b_2281_: *mut LeanObject,
    mut v___y_2282_: *mut LeanObject,
    mut v___y_2283_: *mut LeanObject,
    mut v___y_2284_: *mut LeanObject,
    mut v___y_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: u8 = 0;
    let mut v___x_2292_: u8 = 0;
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2296_: usize = 0;
    let mut v___x_2297_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2287_ = lean_usize_dec_lt(v_i_2280_, v_sz_2279_);
                if v___x_2287_ == 0 {
                    v___x_2288_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2288_, 0, v_b_2281_);
                    return v___x_2288_;
                } else {
                    v___x_2289_ = l_Lean_Meta_Grind_normExt;
                    v_a_2290_ = lean_array_uget_borrowed(v_as_2278_, v_i_2280_);
                    v___x_2291_ = 0;
                    v___x_2292_ = 0;
                    v___x_2293_ = lean_unsigned_to_nat(1000);
                    lean_inc(v_a_2290_);
                    v___x_2294_ = l_Lean_Meta_addSimpTheorem(
                        v___x_2289_,
                        v_a_2290_,
                        v___x_2287_,
                        v___x_2291_,
                        v___x_2292_,
                        v___x_2293_,
                        v___y_2282_,
                        v___y_2283_,
                        v___y_2284_,
                        v___y_2285_,
                    );
                    if lean_obj_tag(v___x_2294_) == 0 {
                        lean_dec_ref_known(v___x_2294_, 1);
                        v___x_2295_ = lean_box(0);
                        v___x_2296_ = 1usize;
                        v___x_2297_ = lean_usize_add(v_i_2280_, v___x_2296_);
                        v_i_2280_ = v___x_2297_;
                        v_b_2281_ = v___x_2295_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2294_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1___boxed(
    mut v_as_2299_: *mut LeanObject,
    mut v_sz_2300_: *mut LeanObject,
    mut v_i_2301_: *mut LeanObject,
    mut v_b_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2308_: usize = 0;
    let mut v_i_boxed_2309_: usize = 0;
    let mut v_res_2310_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2308_ = lean_unbox_usize(v_sz_2300_);
    lean_dec(v_sz_2300_);
    v_i_boxed_2309_ = lean_unbox_usize(v_i_2301_);
    lean_dec(v_i_2301_);
    v_res_2310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_as_2299_, v_sz_boxed_2308_, v_i_boxed_2309_, v_b_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
    lean_dec(v___y_2306_);
    lean_dec_ref(v___y_2305_);
    lean_dec(v___y_2304_);
    lean_dec_ref(v___y_2303_);
    lean_dec_ref(v_as_2299_);
    return v_res_2310_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(
    mut v_as_2311_: *mut LeanObject,
    mut v_sz_2312_: usize,
    mut v_i_2313_: usize,
    mut v_b_2314_: *mut LeanObject,
    mut v___y_2315_: *mut LeanObject,
    mut v___y_2316_: *mut LeanObject,
    mut v___y_2317_: *mut LeanObject,
    mut v___y_2318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2320_: u8 = 0;
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: usize = 0;
    let mut v___x_2330_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2320_ = lean_usize_dec_lt(v_i_2313_, v_sz_2312_);
                if v___x_2320_ == 0 {
                    v___x_2321_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2321_, 0, v_b_2314_);
                    return v___x_2321_;
                } else {
                    v___x_2322_ = l_Lean_Meta_Grind_normExt;
                    v_a_2323_ = lean_array_uget_borrowed(v_as_2311_, v_i_2313_);
                    v___x_2324_ = 0;
                    v___x_2325_ = 0;
                    v___x_2326_ = lean_unsigned_to_nat(1000);
                    lean_inc(v_a_2323_);
                    v___x_2327_ = l_Lean_Meta_addSimpTheorem(
                        v___x_2322_,
                        v_a_2323_,
                        v___x_2324_,
                        v___x_2324_,
                        v___x_2325_,
                        v___x_2326_,
                        v___y_2315_,
                        v___y_2316_,
                        v___y_2317_,
                        v___y_2318_,
                    );
                    if lean_obj_tag(v___x_2327_) == 0 {
                        lean_dec_ref_known(v___x_2327_, 1);
                        v___x_2328_ = lean_box(0);
                        v___x_2329_ = 1usize;
                        v___x_2330_ = lean_usize_add(v_i_2313_, v___x_2329_);
                        v_i_2313_ = v___x_2330_;
                        v_b_2314_ = v___x_2328_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2327_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0___boxed(
    mut v_as_2332_: *mut LeanObject,
    mut v_sz_2333_: *mut LeanObject,
    mut v_i_2334_: *mut LeanObject,
    mut v_b_2335_: *mut LeanObject,
    mut v___y_2336_: *mut LeanObject,
    mut v___y_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2341_: usize = 0;
    let mut v_i_boxed_2342_: usize = 0;
    let mut v_res_2343_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2341_ = lean_unbox_usize(v_sz_2333_);
    lean_dec(v_sz_2333_);
    v_i_boxed_2342_ = lean_unbox_usize(v_i_2334_);
    lean_dec(v_i_2334_);
    v_res_2343_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_as_2332_, v_sz_boxed_2341_, v_i_boxed_2342_, v_b_2335_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
    lean_dec(v___y_2339_);
    lean_dec_ref(v___y_2338_);
    lean_dec(v___y_2337_);
    lean_dec_ref(v___y_2336_);
    lean_dec_ref(v_as_2332_);
    return v_res_2343_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1() -> *mut LeanObject {
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    v___x_2345_ = l_Lean_Meta_Grind_registerNormTheorems___closed__0;
    v___x_2346_ = l_Lean_stringToMessageData(v___x_2345_);
    return v___x_2346_;
}
pub unsafe fn l_Lean_Meta_Grind_registerNormTheorems(
    mut v_preDeclNames_2347_: *mut LeanObject,
    mut v_postDeclNames_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
    mut v_a_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2360_: usize = 0;
    let mut v___x_2361_: usize = 0;
    let mut v___x_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2363_: usize = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2367_: u8 = 0;
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2371_: u8 = 0;
    let mut v_unused_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lemmaNames_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2383_: u8 = 0;
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2373_ = l_Lean_Meta_Grind_normExt;
                v___x_2374_ =
                    l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_2373_, v_a_2352_);
                if lean_obj_tag(v___x_2374_) == 0 {
                    v_a_2375_ = lean_ctor_get(v___x_2374_, 0);
                    lean_inc(v_a_2375_);
                    lean_dec_ref_known(v___x_2374_, 1);
                    v_lemmaNames_2376_ = lean_ctor_get(v_a_2375_, 2);
                    lean_inc_ref(v_lemmaNames_2376_);
                    lean_dec(v_a_2375_);
                    v___x_2377_ =
                        l_Lean_PersistentHashMap_Node_isEmpty___redArg(v_lemmaNames_2376_);
                    lean_dec_ref(v_lemmaNames_2376_);
                    if v___x_2377_ == 0 {
                        v___x_2378_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_registerNormTheorems___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_registerNormTheorems___closed__1_once
                            ),
                            _init_l_Lean_Meta_Grind_registerNormTheorems___closed__1,
                        );
                        v___x_2379_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(v___x_2378_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
                        return v___x_2379_;
                    } else {
                        v___y_2355_ = v_a_2349_;
                        v___y_2356_ = v_a_2350_;
                        v___y_2357_ = v_a_2351_;
                        v___y_2358_ = v_a_2352_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2380_ = lean_ctor_get(v___x_2374_, 0);
                    v_isSharedCheck_2387_ = (!lean_is_exclusive(v___x_2374_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2382_ = v___x_2374_;
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2380_);
                        lean_dec(v___x_2374_);
                        v___x_2382_ = lean_box(0);
                        v_isShared_2383_ = v_isSharedCheck_2387_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2359_ = lean_box(0);
                v_sz_2360_ = lean_array_size(v_preDeclNames_2347_);
                v___x_2361_ = 0usize;
                v___x_2362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__0(v_preDeclNames_2347_, v_sz_2360_, v___x_2361_, v___x_2359_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
                if lean_obj_tag(v___x_2362_) == 0 {
                    lean_dec_ref_known(v___x_2362_, 1);
                    v_sz_2363_ = lean_array_size(v_postDeclNames_2348_);
                    v___x_2364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Grind_registerNormTheorems_spec__1(v_postDeclNames_2348_, v_sz_2363_, v___x_2361_, v___x_2359_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
                    if lean_obj_tag(v___x_2364_) == 0 {
                        v_isSharedCheck_2371_ = (!lean_is_exclusive(v___x_2364_)) as u8;
                        if v_isSharedCheck_2371_ == 0 {
                            v_unused_2372_ = lean_ctor_get(v___x_2364_, 0);
                            lean_dec(v_unused_2372_);
                            v___x_2366_ = v___x_2364_;
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_2364_);
                            v___x_2366_ = lean_box(0);
                            v_isShared_2367_ = v_isSharedCheck_2371_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_2364_;
                    }
                } else {
                    return v___x_2362_;
                }
            }
            2 => {
                if v_isShared_2367_ == 0 {
                    lean_ctor_set(v___x_2366_, 0, v___x_2359_);
                    v___x_2369_ = v___x_2366_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2370_, 0, v___x_2359_);
                    v___x_2369_ = v_reuseFailAlloc_2370_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2369_;
            }
            4 => {
                if v_isShared_2383_ == 0 {
                    v___x_2385_ = v___x_2382_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
                    v___x_2385_ = v_reuseFailAlloc_2386_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_registerNormTheorems___boxed(
    mut v_preDeclNames_2388_: *mut LeanObject,
    mut v_postDeclNames_2389_: *mut LeanObject,
    mut v_a_2390_: *mut LeanObject,
    mut v_a_2391_: *mut LeanObject,
    mut v_a_2392_: *mut LeanObject,
    mut v_a_2393_: *mut LeanObject,
    mut v_a_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2395_: *mut LeanObject = core::ptr::null_mut();
    v_res_2395_ = l_Lean_Meta_Grind_registerNormTheorems(
        v_preDeclNames_2388_,
        v_postDeclNames_2389_,
        v_a_2390_,
        v_a_2391_,
        v_a_2392_,
        v_a_2393_,
    );
    lean_dec(v_a_2393_);
    lean_dec_ref(v_a_2392_);
    lean_dec(v_a_2391_);
    lean_dec_ref(v_a_2390_);
    lean_dec_ref(v_postDeclNames_2389_);
    lean_dec_ref(v_preDeclNames_2388_);
    return v_res_2395_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(
    mut v_00_u03b1_2396_: *mut LeanObject,
    mut v_msg_2397_: *mut LeanObject,
    mut v___y_2398_: *mut LeanObject,
    mut v___y_2399_: *mut LeanObject,
    mut v___y_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    v___x_2403_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___redArg(
        v_msg_2397_,
        v___y_2398_,
        v___y_2399_,
        v___y_2400_,
        v___y_2401_,
    );
    return v___x_2403_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3___boxed(
    mut v_00_u03b1_2404_: *mut LeanObject,
    mut v_msg_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2411_: *mut LeanObject = core::ptr::null_mut();
    v_res_2411_ = l_Lean_throwError___at___00Lean_Meta_Grind_registerNormTheorems_spec__3(
        v_00_u03b1_2404_,
        v_msg_2405_,
        v___y_2406_,
        v___y_2407_,
        v___y_2408_,
        v___y_2409_,
    );
    lean_dec(v___y_2409_);
    lean_dec_ref(v___y_2408_);
    lean_dec(v___y_2407_);
    lean_dec_ref(v___y_2406_);
    return v_res_2411_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(
    mut v_declName_2435_: *mut LeanObject,
) -> u8 {
    let mut v___y_2437_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: u8 = 0;
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: u8 = 0;
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: u8 = 0;
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2444_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__10;
                v___x_2445_ = lean_name_eq(v_declName_2435_, v___x_2444_);
                if v___x_2445_ == 0 {
                    v___x_2446_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__12;
                    v___x_2447_ = lean_name_eq(v_declName_2435_, v___x_2446_);
                    v___y_2437_ = v___x_2447_;
                    state = 1;
                    continue;
                } else {
                    v___y_2437_ = v___x_2445_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v___y_2437_ == 0 {
                    v___x_2438_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__2;
                    v___x_2439_ = lean_name_eq(v_declName_2435_, v___x_2438_);
                    if v___x_2439_ == 0 {
                        v___x_2440_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__5;
                        v___x_2441_ = lean_name_eq(v_declName_2435_, v___x_2440_);
                        if v___x_2441_ == 0 {
                            v___x_2442_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___closed__8;
                            v___x_2443_ = lean_name_eq(v_declName_2435_, v___x_2442_);
                            return v___x_2443_;
                        } else {
                            return v___x_2441_;
                        }
                    } else {
                        return v___x_2439_;
                    }
                } else {
                    return v___y_2437_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget___boxed(
    mut v_declName_2448_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2449_: u8 = 0;
    let mut v_r_2450_: *mut LeanObject = core::ptr::null_mut();
    v_res_2449_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(
        v_declName_2448_,
    );
    lean_dec(v_declName_2448_);
    v_r_2450_ = lean_box((v_res_2449_) as usize);
    return v_r_2450_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6() -> *mut LeanObject {
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    v___x_2461_ = lean_box(0);
    v___x_2462_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
    v___x_2463_ = l_Lean_mkConst(v___x_2462_, v___x_2461_);
    return v___x_2463_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9() -> *mut LeanObject {
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    v___x_2467_ = lean_box(0);
    v___x_2468_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
    v___x_2469_ = l_Lean_mkConst(v___x_2468_, v___x_2467_);
    return v___x_2469_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___x_2477_ = lean_box(0);
    v___x_2478_ = l_Lean_Meta_Grind_simpEq___redArg___closed__13;
    v___x_2479_ = l_Lean_mkConst(v___x_2478_, v___x_2477_);
    return v___x_2479_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut LeanObject = core::ptr::null_mut();
    v___x_2485_ = lean_box(0);
    v___x_2486_ = l_Lean_Meta_Grind_simpEq___redArg___closed__16;
    v___x_2487_ = l_Lean_mkConst(v___x_2486_, v___x_2485_);
    return v___x_2487_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22() -> *mut LeanObject {
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    v___x_2495_ = lean_box(0);
    v___x_2496_ = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
    v___x_2497_ = l_Lean_mkConst(v___x_2496_, v___x_2495_);
    return v___x_2497_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25() -> *mut LeanObject {
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut LeanObject = core::ptr::null_mut();
    v___x_2503_ = lean_box(0);
    v___x_2504_ = l_Lean_Meta_Grind_simpEq___redArg___closed__24;
    v___x_2505_ = l_Lean_mkConst(v___x_2504_, v___x_2503_);
    return v___x_2505_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28() -> *mut LeanObject {
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    v___x_2511_ = lean_box(0);
    v___x_2512_ = l_Lean_Meta_Grind_simpEq___redArg___closed__27;
    v___x_2513_ = l_Lean_mkConst(v___x_2512_, v___x_2511_);
    return v___x_2513_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___redArg(
    mut v_e_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v_a_2520_: *mut LeanObject,
    mut v_a_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2528_: u8 = 0;
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v_arg_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    let mut v_arg_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: u8 = 0;
    let mut v_arg_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u8 = 0;
    let mut v___x_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2550_: u8 = 0;
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: u8 = 0;
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: u8 = 0;
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2595_: u8 = 0;
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2607_: u8 = 0;
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2616_: u8 = 0;
    let mut v_a_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2620_: u8 = 0;
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2624_: u8 = 0;
    let mut v___y_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2627_: u8 = 0;
    let mut v___x_2628_: u8 = 0;
    let mut v___x_2629_: u8 = 0;
    let mut v___x_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2638_: u8 = 0;
    let mut v___x_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: u8 = 0;
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: u8 = 0;
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u8 = 0;
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: u8 = 0;
    let mut v___x_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_a_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2659_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2663_: u8 = 0;
    let mut v_isSharedCheck_2664_: u8 = 0;
    let mut v_a_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2668_: u8 = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2524_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2518_, v_a_2520_);
                if lean_obj_tag(v___x_2524_) == 0 {
                    v_a_2525_ = lean_ctor_get(v___x_2524_, 0);
                    v_isSharedCheck_2664_ = (!lean_is_exclusive(v___x_2524_)) as u8;
                    if v_isSharedCheck_2664_ == 0 {
                        v___x_2527_ = v___x_2524_;
                        v_isShared_2528_ = v_isSharedCheck_2664_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2525_);
                        lean_dec(v___x_2524_);
                        v___x_2527_ = lean_box(0);
                        v_isShared_2528_ = v_isSharedCheck_2664_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2665_ = lean_ctor_get(v___x_2524_, 0);
                    v_isSharedCheck_2672_ = (!lean_is_exclusive(v___x_2524_)) as u8;
                    if v_isSharedCheck_2672_ == 0 {
                        v___x_2667_ = v___x_2524_;
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 20;
                        continue;
                    } else {
                        lean_inc(v_a_2665_);
                        lean_dec(v___x_2524_);
                        v___x_2667_ = lean_box(0);
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2534_ = l_Lean_Expr_cleanupAnnotations(v_a_2525_);
                v___x_2535_ = l_Lean_Expr_isApp(v___x_2534_);
                if v___x_2535_ == 0 {
                    lean_dec_ref(v___x_2534_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2536_ = lean_ctor_get(v___x_2534_, 1);
                    lean_inc_ref(v_arg_2536_);
                    v___x_2537_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2534_);
                    v___x_2538_ = l_Lean_Expr_isApp(v___x_2537_);
                    if v___x_2538_ == 0 {
                        lean_dec_ref(v___x_2537_);
                        lean_dec_ref(v_arg_2536_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2539_ = lean_ctor_get(v___x_2537_, 1);
                        lean_inc_ref(v_arg_2539_);
                        v___x_2540_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2537_);
                        v___x_2541_ = l_Lean_Expr_isApp(v___x_2540_);
                        if v___x_2541_ == 0 {
                            lean_dec_ref(v___x_2540_);
                            lean_dec_ref(v_arg_2539_);
                            lean_dec_ref(v_arg_2536_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2542_ = lean_ctor_get(v___x_2540_, 1);
                            lean_inc_ref(v_arg_2542_);
                            v___x_2543_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2540_);
                            v___x_2544_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                            v___x_2545_ = l_Lean_Expr_isConstOf(v___x_2543_, v___x_2544_);
                            if v___x_2545_ == 0 {
                                lean_dec_ref(v___x_2543_);
                                lean_dec_ref(v_arg_2542_);
                                lean_dec_ref(v_arg_2539_);
                                lean_dec_ref(v_arg_2536_);
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_2527_);
                                lean_inc_ref(v_arg_2542_);
                                v___x_2546_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                    v_arg_2542_,
                                    v_a_2520_,
                                );
                                if lean_obj_tag(v___x_2546_) == 0 {
                                    v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
                                    v_isSharedCheck_2655_ = (!lean_is_exclusive(v___x_2546_)) as u8;
                                    if v_isSharedCheck_2655_ == 0 {
                                        v___x_2549_ = v___x_2546_;
                                        v_isShared_2550_ = v_isSharedCheck_2655_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2547_);
                                        lean_dec(v___x_2546_);
                                        v___x_2549_ = lean_box(0);
                                        v_isShared_2550_ = v_isSharedCheck_2655_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v___x_2543_);
                                    lean_dec_ref(v_arg_2542_);
                                    lean_dec_ref(v_arg_2539_);
                                    lean_dec_ref(v_arg_2536_);
                                    v_a_2656_ = lean_ctor_get(v___x_2546_, 0);
                                    v_isSharedCheck_2663_ = (!lean_is_exclusive(v___x_2546_)) as u8;
                                    if v_isSharedCheck_2663_ == 0 {
                                        v___x_2658_ = v___x_2546_;
                                        v_isShared_2659_ = v_isSharedCheck_2663_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2656_);
                                        lean_dec(v___x_2546_);
                                        v___x_2658_ = lean_box(0);
                                        v_isShared_2659_ = v_isSharedCheck_2663_;
                                        state = 18;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2530_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_2528_ == 0 {
                    lean_ctor_set(v___x_2527_, 0, v___x_2530_);
                    v___x_2532_ = v___x_2527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2530_);
                    v___x_2532_ = v_reuseFailAlloc_2533_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2532_;
            }
            4 => {
                v___x_2551_ = l_Lean_Expr_cleanupAnnotations(v_a_2547_);
                v___x_2552_ = l_Lean_Meta_Grind_simpEq___redArg___closed__3;
                v___x_2553_ = l_Lean_Expr_isConstOf(v___x_2551_, v___x_2552_);
                lean_dec_ref(v___x_2551_);
                if v___x_2553_ == 0 {
                    v___x_2554_ = lean_expr_eqv(v_arg_2539_, v_arg_2536_);
                    if v___x_2554_ == 0 {
                        lean_dec_ref(v___x_2543_);
                        lean_dec_ref(v_arg_2542_);
                        v___x_2555_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                        );
                        v___x_2556_ = lean_expr_eqv(v_arg_2536_, v___x_2555_);
                        if v___x_2556_ == 0 {
                            v___x_2557_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__9_once
                                ),
                                _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                            );
                            v___x_2558_ = lean_expr_eqv(v_arg_2536_, v___x_2557_);
                            lean_dec_ref(v_arg_2536_);
                            if v___x_2558_ == 0 {
                                lean_dec_ref(v_arg_2539_);
                                v___x_2559_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                if v_isShared_2550_ == 0 {
                                    lean_ctor_set(v___x_2549_, 0, v___x_2559_);
                                    v___x_2561_ = v___x_2549_;
                                    state = 5;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2559_);
                                    v___x_2561_ = v_reuseFailAlloc_2562_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_inc_ref(v_arg_2539_);
                                v___x_2563_ = l_Lean_mkNot(v_arg_2539_);
                                v___x_2564_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_simpEq___redArg___closed__14
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_simpEq___redArg___closed__14_once
                                    ),
                                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__14,
                                );
                                v___x_2565_ = l_Lean_Expr_app___override(v___x_2564_, v_arg_2539_);
                                v___x_2566_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2566_, 0, v___x_2565_);
                                v___x_2567_ = lean_alloc_ctor(0, 2, (1) as u32);
                                lean_ctor_set(v___x_2567_, 0, v___x_2563_);
                                lean_ctor_set(v___x_2567_, 1, v___x_2566_);
                                lean_ctor_set_uint8(
                                    v___x_2567_,
                                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                    v___x_2545_,
                                );
                                v___x_2568_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2568_, 0, v___x_2567_);
                                if v_isShared_2550_ == 0 {
                                    lean_ctor_set(v___x_2549_, 0, v___x_2568_);
                                    v___x_2570_ = v___x_2549_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_2571_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_2571_, 0, v___x_2568_);
                                    v___x_2570_ = v_reuseFailAlloc_2571_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_arg_2536_);
                            v___x_2572_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__17
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_simpEq___redArg___closed__17_once
                                ),
                                _init_l_Lean_Meta_Grind_simpEq___redArg___closed__17,
                            );
                            lean_inc_ref(v_arg_2539_);
                            v___x_2573_ = l_Lean_Expr_app___override(v___x_2572_, v_arg_2539_);
                            v___x_2574_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2574_, 0, v___x_2573_);
                            v___x_2575_ = lean_alloc_ctor(0, 2, (1) as u32);
                            lean_ctor_set(v___x_2575_, 0, v_arg_2539_);
                            lean_ctor_set(v___x_2575_, 1, v___x_2574_);
                            lean_ctor_set_uint8(
                                v___x_2575_,
                                (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                v___x_2545_,
                            );
                            v___x_2576_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2576_, 0, v___x_2575_);
                            if v_isShared_2550_ == 0 {
                                lean_ctor_set(v___x_2549_, 0, v___x_2576_);
                                v___x_2578_ = v___x_2549_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_2579_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2579_, 0, v___x_2576_);
                                v___x_2578_ = v_reuseFailAlloc_2579_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_arg_2536_);
                        v___x_2580_ = l_Lean_Expr_constLevels_x21(v___x_2543_);
                        lean_dec_ref(v___x_2543_);
                        v___x_2581_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                        );
                        v___x_2582_ = l_Lean_Meta_Grind_simpEq___redArg___closed__19;
                        v___x_2583_ = l_Lean_mkConst(v___x_2582_, v___x_2580_);
                        v___x_2584_ = l_Lean_mkAppB(v___x_2583_, v_arg_2542_, v_arg_2539_);
                        v___x_2585_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2585_, 0, v___x_2584_);
                        v___x_2586_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_2586_, 0, v___x_2581_);
                        lean_ctor_set(v___x_2586_, 1, v___x_2585_);
                        lean_ctor_set_uint8(
                            v___x_2586_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_2545_,
                        );
                        v___x_2587_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2587_, 0, v___x_2586_);
                        if v_isShared_2550_ == 0 {
                            lean_ctor_set(v___x_2549_, 0, v___x_2587_);
                            v___x_2589_ = v___x_2549_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_2590_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2590_, 0, v___x_2587_);
                            v___x_2589_ = v_reuseFailAlloc_2590_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    v___x_2591_ = l_Lean_Expr_getAppFn(v_arg_2536_);
                    if lean_obj_tag(v___x_2591_) == 4 {
                        v_declName_2592_ = lean_ctor_get(v___x_2591_, 0);
                        lean_inc(v_declName_2592_);
                        lean_dec_ref_known(v___x_2591_, 2);
                        v___x_2593_ = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
                        v___x_2648_ = lean_name_eq(v_declName_2592_, v___x_2593_);
                        if v___x_2648_ == 0 {
                            v___x_2649_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
                            v___x_2650_ = lean_name_eq(v_declName_2592_, v___x_2649_);
                            v___y_2638_ = v___x_2650_;
                            state = 16;
                            continue;
                        } else {
                            v___y_2638_ = v___x_2648_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2591_);
                        lean_dec_ref(v___x_2543_);
                        lean_dec_ref(v_arg_2542_);
                        lean_dec_ref(v_arg_2539_);
                        lean_dec_ref(v_arg_2536_);
                        v___x_2651_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_2550_ == 0 {
                            lean_ctor_set(v___x_2549_, 0, v___x_2651_);
                            v___x_2653_ = v___x_2549_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_2654_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2654_, 0, v___x_2651_);
                            v___x_2653_ = v_reuseFailAlloc_2654_;
                            state = 17;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_2561_;
            }
            6 => {
                return v___x_2570_;
            }
            7 => {
                return v___x_2578_;
            }
            8 => {
                return v___x_2589_;
            }
            9 => {
                if v___y_2595_ == 0 {
                    lean_dec_ref(v___x_2543_);
                    lean_dec_ref(v_arg_2542_);
                    lean_dec_ref(v_arg_2539_);
                    lean_dec_ref(v_arg_2536_);
                    v___x_2596_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_2550_ == 0 {
                        lean_ctor_set(v___x_2549_, 0, v___x_2596_);
                        v___x_2598_ = v___x_2549_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2599_, 0, v___x_2596_);
                        v___x_2598_ = v_reuseFailAlloc_2599_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2549_);
                    v___x_2600_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__22_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22,
                    );
                    lean_inc_ref(v_arg_2539_);
                    lean_inc_ref(v_arg_2542_);
                    lean_inc_ref(v___x_2543_);
                    v___x_2601_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2539_, v___x_2600_);
                    lean_inc_ref(v_arg_2536_);
                    v___x_2602_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2536_, v___x_2600_);
                    v___x_2603_ = l_Lean_Meta_mkEq(
                        v___x_2601_,
                        v___x_2602_,
                        v_a_2519_,
                        v_a_2520_,
                        v_a_2521_,
                        v_a_2522_,
                    );
                    if lean_obj_tag(v___x_2603_) == 0 {
                        v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
                        v_isSharedCheck_2616_ = (!lean_is_exclusive(v___x_2603_)) as u8;
                        if v_isSharedCheck_2616_ == 0 {
                            v___x_2606_ = v___x_2603_;
                            v_isShared_2607_ = v_isSharedCheck_2616_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2604_);
                            lean_dec(v___x_2603_);
                            v___x_2606_ = lean_box(0);
                            v_isShared_2607_ = v_isSharedCheck_2616_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_arg_2539_);
                        lean_dec_ref(v_arg_2536_);
                        v_a_2617_ = lean_ctor_get(v___x_2603_, 0);
                        v_isSharedCheck_2624_ = (!lean_is_exclusive(v___x_2603_)) as u8;
                        if v_isSharedCheck_2624_ == 0 {
                            v___x_2619_ = v___x_2603_;
                            v_isShared_2620_ = v_isSharedCheck_2624_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_2617_);
                            lean_dec(v___x_2603_);
                            v___x_2619_ = lean_box(0);
                            v_isShared_2620_ = v_isSharedCheck_2624_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            10 => {
                return v___x_2598_;
            }
            11 => {
                v___x_2608_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__25),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__25_once),
                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__25,
                );
                v___x_2609_ = l_Lean_mkAppB(v___x_2608_, v_arg_2539_, v_arg_2536_);
                v___x_2610_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2610_, 0, v___x_2609_);
                v___x_2611_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_2611_, 0, v_a_2604_);
                lean_ctor_set(v___x_2611_, 1, v___x_2610_);
                lean_ctor_set_uint8(
                    v___x_2611_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_2553_,
                );
                v___x_2612_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2612_, 0, v___x_2611_);
                if v_isShared_2607_ == 0 {
                    lean_ctor_set(v___x_2606_, 0, v___x_2612_);
                    v___x_2614_ = v___x_2606_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2615_, 0, v___x_2612_);
                    v___x_2614_ = v_reuseFailAlloc_2615_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2614_;
            }
            13 => {
                if v_isShared_2620_ == 0 {
                    v___x_2622_ = v___x_2619_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
                    v___x_2622_ = v_reuseFailAlloc_2623_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2622_;
            }
            15 => {
                if v___y_2627_ == 0 {
                    v___x_2628_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v___y_2626_);
                    lean_dec(v___y_2626_);
                    if v___x_2628_ == 0 {
                        v___x_2629_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_isBoolEqTarget(v_declName_2592_);
                        lean_dec(v_declName_2592_);
                        v___y_2595_ = v___x_2629_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v_declName_2592_);
                        v___y_2595_ = v___x_2628_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2626_);
                    lean_dec(v_declName_2592_);
                    lean_del_object(v___x_2549_);
                    lean_inc_ref(v_arg_2539_);
                    lean_inc_ref(v_arg_2536_);
                    v___x_2630_ = l_Lean_mkApp3(v___x_2543_, v_arg_2542_, v_arg_2536_, v_arg_2539_);
                    v___x_2631_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__28),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__28_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__28,
                    );
                    v___x_2632_ = l_Lean_mkAppB(v___x_2631_, v_arg_2539_, v_arg_2536_);
                    v___x_2633_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2633_, 0, v___x_2632_);
                    v___x_2634_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_2634_, 0, v___x_2630_);
                    lean_ctor_set(v___x_2634_, 1, v___x_2633_);
                    lean_ctor_set_uint8(
                        v___x_2634_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_2553_,
                    );
                    v___x_2635_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2635_, 0, v___x_2634_);
                    v___x_2636_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2636_, 0, v___x_2635_);
                    return v___x_2636_;
                }
            }
            16 => {
                if v___y_2638_ == 0 {
                    v___x_2639_ = l_Lean_Expr_getAppFn(v_arg_2539_);
                    if lean_obj_tag(v___x_2639_) == 4 {
                        v_declName_2640_ = lean_ctor_get(v___x_2639_, 0);
                        lean_inc(v_declName_2640_);
                        lean_dec_ref_known(v___x_2639_, 2);
                        v___x_2641_ = lean_name_eq(v_declName_2640_, v___x_2593_);
                        if v___x_2641_ == 0 {
                            v___x_2642_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
                            v___x_2643_ = lean_name_eq(v_declName_2640_, v___x_2642_);
                            v___y_2626_ = v_declName_2640_;
                            v___y_2627_ = v___x_2643_;
                            state = 15;
                            continue;
                        } else {
                            v___y_2626_ = v_declName_2640_;
                            v___y_2627_ = v___x_2641_;
                            state = 15;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_2639_);
                        lean_dec(v_declName_2592_);
                        lean_del_object(v___x_2549_);
                        lean_dec_ref(v___x_2543_);
                        lean_dec_ref(v_arg_2542_);
                        lean_dec_ref(v_arg_2539_);
                        lean_dec_ref(v_arg_2536_);
                        v___x_2644_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        v___x_2645_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2645_, 0, v___x_2644_);
                        return v___x_2645_;
                    }
                } else {
                    lean_dec(v_declName_2592_);
                    lean_del_object(v___x_2549_);
                    lean_dec_ref(v___x_2543_);
                    lean_dec_ref(v_arg_2542_);
                    lean_dec_ref(v_arg_2539_);
                    lean_dec_ref(v_arg_2536_);
                    v___x_2646_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    v___x_2647_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2647_, 0, v___x_2646_);
                    return v___x_2647_;
                }
            }
            17 => {
                return v___x_2653_;
            }
            18 => {
                if v_isShared_2659_ == 0 {
                    v___x_2661_ = v___x_2658_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2662_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2662_, 0, v_a_2656_);
                    v___x_2661_ = v_reuseFailAlloc_2662_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2661_;
            }
            20 => {
                if v_isShared_2668_ == 0 {
                    v___x_2670_ = v___x_2667_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
                    v___x_2670_ = v_reuseFailAlloc_2671_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___redArg___boxed(
    mut v_e_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
    mut v_a_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2679_: *mut LeanObject = core::ptr::null_mut();
    v_res_2679_ =
        l_Lean_Meta_Grind_simpEq___redArg(v_e_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
    lean_dec(v_a_2677_);
    lean_dec_ref(v_a_2676_);
    lean_dec(v_a_2675_);
    lean_dec_ref(v_a_2674_);
    return v_res_2679_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq(
    mut v_e_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
    mut v_a_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
    mut v_a_2687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    v___x_2689_ =
        l_Lean_Meta_Grind_simpEq___redArg(v_e_2680_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
    return v___x_2689_;
}
pub unsafe fn l_Lean_Meta_Grind_simpEq___boxed(
    mut v_e_2690_: *mut LeanObject,
    mut v_a_2691_: *mut LeanObject,
    mut v_a_2692_: *mut LeanObject,
    mut v_a_2693_: *mut LeanObject,
    mut v_a_2694_: *mut LeanObject,
    mut v_a_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
    mut v_a_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2699_: *mut LeanObject = core::ptr::null_mut();
    v_res_2699_ = l_Lean_Meta_Grind_simpEq(
        v_e_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_,
    );
    lean_dec(v_a_2697_);
    lean_dec_ref(v_a_2696_);
    lean_dec(v_a_2695_);
    lean_dec_ref(v_a_2694_);
    lean_dec(v_a_2693_);
    lean_dec_ref(v_a_2692_);
    lean_dec(v_a_2691_);
    return v_res_2699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_()
-> *mut LeanObject {
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    v___x_2719_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_2720_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_2721_ = lean_alloc_closure(
        l_Lean_Meta_Grind_simpEq___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2722_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2719_, v___x_2720_, v___x_2721_);
    return v___x_2722_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12____boxed(
    mut v_a_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2724_: *mut LeanObject = core::ptr::null_mut();
    v_res_2724_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_();
    return v_res_2724_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___redArg(
    mut v_e_2734_: *mut LeanObject,
    mut v_a_2735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: u8 = 0;
    let mut v_arg_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: u8 = 0;
    let mut v_arg_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: u8 = 0;
    let mut v_arg_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: u8 = 0;
    let mut v_arg_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: u8 = 0;
    let mut v_arg_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: u8 = 0;
    let mut v_body_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: u8 = 0;
    let mut v_body_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2788_: u8 = 0;
    let mut v_a_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2737_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2734_, v_a_2735_);
                if lean_obj_tag(v___x_2737_) == 0 {
                    v_a_2738_ = lean_ctor_get(v___x_2737_, 0);
                    v_isSharedCheck_2788_ = (!lean_is_exclusive(v___x_2737_)) as u8;
                    if v_isSharedCheck_2788_ == 0 {
                        v___x_2740_ = v___x_2737_;
                        v_isShared_2741_ = v_isSharedCheck_2788_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2738_);
                        lean_dec(v___x_2737_);
                        v___x_2740_ = lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2788_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2789_ = lean_ctor_get(v___x_2737_, 0);
                    v_isSharedCheck_2796_ = (!lean_is_exclusive(v___x_2737_)) as u8;
                    if v_isSharedCheck_2796_ == 0 {
                        v___x_2791_ = v___x_2737_;
                        v_isShared_2792_ = v_isSharedCheck_2796_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2789_);
                        lean_dec(v___x_2737_);
                        v___x_2791_ = lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2796_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2747_ = l_Lean_Expr_cleanupAnnotations(v_a_2738_);
                v___x_2748_ = l_Lean_Expr_isApp(v___x_2747_);
                if v___x_2748_ == 0 {
                    lean_dec_ref(v___x_2747_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2749_ = lean_ctor_get(v___x_2747_, 1);
                    lean_inc_ref(v_arg_2749_);
                    v___x_2750_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2747_);
                    v___x_2751_ = l_Lean_Expr_isApp(v___x_2750_);
                    if v___x_2751_ == 0 {
                        lean_dec_ref(v___x_2750_);
                        lean_dec_ref(v_arg_2749_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2752_ = lean_ctor_get(v___x_2750_, 1);
                        lean_inc_ref(v_arg_2752_);
                        v___x_2753_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2750_);
                        v___x_2754_ = l_Lean_Expr_isApp(v___x_2753_);
                        if v___x_2754_ == 0 {
                            lean_dec_ref(v___x_2753_);
                            lean_dec_ref(v_arg_2752_);
                            lean_dec_ref(v_arg_2749_);
                            state = 2;
                            continue;
                        } else {
                            v_arg_2755_ = lean_ctor_get(v___x_2753_, 1);
                            lean_inc_ref(v_arg_2755_);
                            v___x_2756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2753_);
                            v___x_2757_ = l_Lean_Expr_isApp(v___x_2756_);
                            if v___x_2757_ == 0 {
                                lean_dec_ref(v___x_2756_);
                                lean_dec_ref(v_arg_2755_);
                                lean_dec_ref(v_arg_2752_);
                                lean_dec_ref(v_arg_2749_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_2758_ = lean_ctor_get(v___x_2756_, 1);
                                lean_inc_ref(v_arg_2758_);
                                v___x_2759_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2756_);
                                v___x_2760_ = l_Lean_Expr_isApp(v___x_2759_);
                                if v___x_2760_ == 0 {
                                    lean_dec_ref(v___x_2759_);
                                    lean_dec_ref(v_arg_2758_);
                                    lean_dec_ref(v_arg_2755_);
                                    lean_dec_ref(v_arg_2752_);
                                    lean_dec_ref(v_arg_2749_);
                                    state = 2;
                                    continue;
                                } else {
                                    v_arg_2761_ = lean_ctor_get(v___x_2759_, 1);
                                    lean_inc_ref(v_arg_2761_);
                                    v___x_2762_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2759_);
                                    v___x_2763_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__1;
                                    v___x_2764_ = l_Lean_Expr_isConstOf(v___x_2762_, v___x_2763_);
                                    if v___x_2764_ == 0 {
                                        lean_dec_ref(v___x_2762_);
                                        lean_dec_ref(v_arg_2761_);
                                        lean_dec_ref(v_arg_2758_);
                                        lean_dec_ref(v_arg_2755_);
                                        lean_dec_ref(v_arg_2752_);
                                        lean_dec_ref(v_arg_2749_);
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_del_object(v___x_2740_);
                                        if lean_obj_tag(v_arg_2752_) == 6 {
                                            v_body_2765_ = lean_ctor_get(v_arg_2752_, 2);
                                            lean_inc_ref(v_body_2765_);
                                            lean_dec_ref_known(v_arg_2752_, 3);
                                            v___x_2766_ = l_Lean_Expr_hasLooseBVars(v_body_2765_);
                                            if v___x_2766_ == 0 {
                                                if lean_obj_tag(v_arg_2749_) == 6 {
                                                    v_body_2767_ = lean_ctor_get(v_arg_2749_, 2);
                                                    lean_inc_ref(v_body_2767_);
                                                    lean_dec_ref_known(v_arg_2749_, 3);
                                                    v___x_2768_ =
                                                        l_Lean_Expr_hasLooseBVars(v_body_2767_);
                                                    if v___x_2768_ == 0 {
                                                        v___x_2769_ = l_Lean_Expr_constLevels_x21(
                                                            v___x_2762_,
                                                        );
                                                        lean_dec_ref(v___x_2762_);
                                                        v___x_2770_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
                                                        lean_inc(v___x_2769_);
                                                        v___x_2771_ = l_Lean_mkConst(
                                                            v___x_2770_,
                                                            v___x_2769_,
                                                        );
                                                        lean_inc_ref(v_body_2767_);
                                                        lean_inc_ref(v_body_2765_);
                                                        lean_inc_ref(v_arg_2755_);
                                                        lean_inc_ref(v_arg_2758_);
                                                        lean_inc_ref(v_arg_2761_);
                                                        v___x_2772_ = l_Lean_mkApp5(
                                                            v___x_2771_,
                                                            v_arg_2761_,
                                                            v_arg_2758_,
                                                            v_arg_2755_,
                                                            v_body_2765_,
                                                            v_body_2767_,
                                                        );
                                                        v___x_2773_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__5;
                                                        v___x_2774_ = l_Lean_mkConst(
                                                            v___x_2773_,
                                                            v___x_2769_,
                                                        );
                                                        v___x_2775_ = l_Lean_mkApp5(
                                                            v___x_2774_,
                                                            v_arg_2758_,
                                                            v_arg_2761_,
                                                            v_body_2765_,
                                                            v_body_2767_,
                                                            v_arg_2755_,
                                                        );
                                                        v___x_2776_ =
                                                            lean_alloc_ctor(1, 1, (0) as u32);
                                                        lean_ctor_set(v___x_2776_, 0, v___x_2775_);
                                                        v___x_2777_ =
                                                            lean_alloc_ctor(0, 2, (1) as u32);
                                                        lean_ctor_set(v___x_2777_, 0, v___x_2772_);
                                                        lean_ctor_set(v___x_2777_, 1, v___x_2776_);
                                                        lean_ctor_set_uint8(
                                                            v___x_2777_,
                                                            (core::mem::size_of::<*mut LeanObject>(
                                                            ) * 2)
                                                                as u32,
                                                            v___x_2764_,
                                                        );
                                                        v___x_2778_ =
                                                            lean_alloc_ctor(1, 1, (0) as u32);
                                                        lean_ctor_set(v___x_2778_, 0, v___x_2777_);
                                                        v___x_2779_ =
                                                            lean_alloc_ctor(0, 1, (0) as u32);
                                                        lean_ctor_set(v___x_2779_, 0, v___x_2778_);
                                                        return v___x_2779_;
                                                    } else {
                                                        lean_dec_ref(v_body_2767_);
                                                        lean_dec_ref(v_body_2765_);
                                                        lean_dec_ref(v___x_2762_);
                                                        lean_dec_ref(v_arg_2761_);
                                                        lean_dec_ref(v_arg_2758_);
                                                        lean_dec_ref(v_arg_2755_);
                                                        v___x_2780_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                        v___x_2781_ =
                                                            lean_alloc_ctor(0, 1, (0) as u32);
                                                        lean_ctor_set(v___x_2781_, 0, v___x_2780_);
                                                        return v___x_2781_;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_body_2765_);
                                                    lean_dec_ref(v___x_2762_);
                                                    lean_dec_ref(v_arg_2761_);
                                                    lean_dec_ref(v_arg_2758_);
                                                    lean_dec_ref(v_arg_2755_);
                                                    lean_dec_ref(v_arg_2749_);
                                                    v___x_2782_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                    v___x_2783_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(v___x_2783_, 0, v___x_2782_);
                                                    return v___x_2783_;
                                                }
                                            } else {
                                                lean_dec_ref(v_body_2765_);
                                                lean_dec_ref(v___x_2762_);
                                                lean_dec_ref(v_arg_2761_);
                                                lean_dec_ref(v_arg_2758_);
                                                lean_dec_ref(v_arg_2755_);
                                                lean_dec_ref(v_arg_2749_);
                                                v___x_2784_ =
                                                    l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                v___x_2785_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(v___x_2785_, 0, v___x_2784_);
                                                return v___x_2785_;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_2762_);
                                            lean_dec_ref(v_arg_2761_);
                                            lean_dec_ref(v_arg_2758_);
                                            lean_dec_ref(v_arg_2755_);
                                            lean_dec_ref(v_arg_2752_);
                                            lean_dec_ref(v_arg_2749_);
                                            v___x_2786_ =
                                                l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                            v___x_2787_ = lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v___x_2787_, 0, v___x_2786_);
                                            return v___x_2787_;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2743_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_2741_ == 0 {
                    lean_ctor_set(v___x_2740_, 0, v___x_2743_);
                    v___x_2745_ = v___x_2740_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2746_, 0, v___x_2743_);
                    v___x_2745_ = v_reuseFailAlloc_2746_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2745_;
            }
            4 => {
                if v_isShared_2792_ == 0 {
                    v___x_2794_ = v___x_2791_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2795_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_a_2789_);
                    v___x_2794_ = v_reuseFailAlloc_2795_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2794_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___redArg___boxed(
    mut v_e_2797_: *mut LeanObject,
    mut v_a_2798_: *mut LeanObject,
    mut v_a_2799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2800_: *mut LeanObject = core::ptr::null_mut();
    v_res_2800_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_2797_, v_a_2798_);
    lean_dec(v_a_2798_);
    return v_res_2800_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte(
    mut v_e_2801_: *mut LeanObject,
    mut v_a_2802_: *mut LeanObject,
    mut v_a_2803_: *mut LeanObject,
    mut v_a_2804_: *mut LeanObject,
    mut v_a_2805_: *mut LeanObject,
    mut v_a_2806_: *mut LeanObject,
    mut v_a_2807_: *mut LeanObject,
    mut v_a_2808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2810_: *mut LeanObject = core::ptr::null_mut();
    v___x_2810_ = l_Lean_Meta_Grind_simpDIte___redArg(v_e_2801_, v_a_2806_);
    return v___x_2810_;
}
pub unsafe fn l_Lean_Meta_Grind_simpDIte___boxed(
    mut v_e_2811_: *mut LeanObject,
    mut v_a_2812_: *mut LeanObject,
    mut v_a_2813_: *mut LeanObject,
    mut v_a_2814_: *mut LeanObject,
    mut v_a_2815_: *mut LeanObject,
    mut v_a_2816_: *mut LeanObject,
    mut v_a_2817_: *mut LeanObject,
    mut v_a_2818_: *mut LeanObject,
    mut v_a_2819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2820_: *mut LeanObject = core::ptr::null_mut();
    v_res_2820_ = l_Lean_Meta_Grind_simpDIte(
        v_e_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_,
    );
    lean_dec(v_a_2818_);
    lean_dec_ref(v_a_2817_);
    lean_dec(v_a_2816_);
    lean_dec_ref(v_a_2815_);
    lean_dec(v_a_2814_);
    lean_dec_ref(v_a_2813_);
    lean_dec(v_a_2812_);
    return v_res_2820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_()
-> *mut LeanObject {
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    v___x_2841_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
    v___x_2842_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
    v___x_2843_ = lean_alloc_closure(
        l_Lean_Meta_Grind_simpDIte___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_2844_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_2841_, v___x_2842_, v___x_2843_);
    return v___x_2844_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13____boxed(
    mut v_a_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2846_: *mut LeanObject = core::ptr::null_mut();
    v_res_2846_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_();
    return v_res_2846_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    v___x_2863_ = lean_box(0);
    v___x_2864_ = l_Lean_Meta_Grind_pushNot___redArg___closed__7;
    v___x_2865_ = l_Lean_mkConst(v___x_2864_, v___x_2863_);
    return v___x_2865_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18() -> *mut LeanObject {
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    v___x_2882_ = lean_box(0);
    v___x_2883_ = l_Lean_Meta_Grind_pushNot___redArg___closed__17;
    v___x_2884_ = l_Lean_mkConst(v___x_2883_, v___x_2882_);
    return v___x_2884_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23() -> *mut LeanObject {
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    v___x_2891_ = lean_unsigned_to_nat(1);
    v___x_2892_ = lean_nat_to_int(v___x_2891_);
    return v___x_2892_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24() -> *mut LeanObject {
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    v___x_2893_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__23_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__23,
    );
    v___x_2894_ = l_Lean_mkIntLit(v___x_2893_);
    return v___x_2894_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27() -> *mut LeanObject {
    let mut v___x_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    v___x_2899_ = lean_box(0);
    v___x_2900_ = l_Lean_Meta_Grind_pushNot___redArg___closed__26;
    v___x_2901_ = l_Lean_mkConst(v___x_2900_, v___x_2899_);
    return v___x_2901_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28() -> *mut LeanObject {
    let mut v___x_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    v___x_2902_ = lean_unsigned_to_nat(1);
    v___x_2903_ = l_Lean_mkNatLit(v___x_2902_);
    return v___x_2903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30() -> *mut LeanObject {
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v___x_2907_ = lean_box(0);
    v___x_2908_ = l_Lean_Meta_Grind_pushNot___redArg___closed__29;
    v___x_2909_ = l_Lean_mkConst(v___x_2908_, v___x_2907_);
    return v___x_2909_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31() -> *mut LeanObject {
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    v___x_2910_ = lean_box(0);
    v___x_2911_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
    v___x_2912_ = l_Lean_mkConst(v___x_2911_, v___x_2910_);
    return v___x_2912_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34() -> *mut LeanObject {
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    v___x_2917_ = lean_box(0);
    v___x_2918_ = l_Lean_Meta_Grind_pushNot___redArg___closed__33;
    v___x_2919_ = l_Lean_mkConst(v___x_2918_, v___x_2917_);
    return v___x_2919_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37() -> *mut LeanObject {
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    v___x_2924_ = lean_box(0);
    v___x_2925_ = l_Lean_Meta_Grind_pushNot___redArg___closed__36;
    v___x_2926_ = l_Lean_mkConst(v___x_2925_, v___x_2924_);
    return v___x_2926_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40() -> *mut LeanObject {
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    v___x_2932_ = lean_box(0);
    v___x_2933_ = l_Lean_Meta_Grind_pushNot___redArg___closed__39;
    v___x_2934_ = l_Lean_mkConst(v___x_2933_, v___x_2932_);
    return v___x_2934_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41() -> *mut LeanObject {
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    v___x_2935_ = lean_box(0);
    v___x_2936_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
    v___x_2937_ = l_Lean_mkConst(v___x_2936_, v___x_2935_);
    return v___x_2937_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44() -> *mut LeanObject {
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    v___x_2943_ = lean_box(0);
    v___x_2944_ = l_Lean_Meta_Grind_pushNot___redArg___closed__43;
    v___x_2945_ = l_Lean_mkConst(v___x_2944_, v___x_2943_);
    return v___x_2945_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45() -> *mut LeanObject {
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    v___x_2946_ = lean_box(0);
    v___x_2947_ = l_Lean_Meta_Grind_pushNot___redArg___closed__12;
    v___x_2948_ = l_Lean_mkConst(v___x_2947_, v___x_2946_);
    return v___x_2948_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48() -> *mut LeanObject {
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    v___x_2954_ = lean_box(0);
    v___x_2955_ = l_Lean_Meta_Grind_pushNot___redArg___closed__47;
    v___x_2956_ = l_Lean_mkConst(v___x_2955_, v___x_2954_);
    return v___x_2956_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51() -> *mut LeanObject {
    let mut v___x_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    v___x_2960_ = lean_unsigned_to_nat(0);
    v___x_2961_ = l_Lean_mkBVar(v___x_2960_);
    return v___x_2961_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56() -> *mut LeanObject {
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    v___x_2972_ = lean_box(0);
    v___x_2973_ = l_Lean_Meta_Grind_pushNot___redArg___closed__55;
    v___x_2974_ = l_Lean_mkConst(v___x_2973_, v___x_2972_);
    return v___x_2974_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59() -> *mut LeanObject {
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    v___x_2980_ = lean_box(0);
    v___x_2981_ = l_Lean_Meta_Grind_pushNot___redArg___closed__58;
    v___x_2982_ = l_Lean_mkConst(v___x_2981_, v___x_2980_);
    return v___x_2982_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60() -> *mut LeanObject {
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    v___x_2983_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__59),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__59_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__59,
    );
    v___x_2984_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2984_, 0, v___x_2983_);
    return v___x_2984_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63() -> *mut LeanObject {
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    v___x_2990_ = lean_box(0);
    v___x_2991_ = l_Lean_Meta_Grind_pushNot___redArg___closed__62;
    v___x_2992_ = l_Lean_mkConst(v___x_2991_, v___x_2990_);
    return v___x_2992_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64() -> *mut LeanObject {
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut LeanObject = core::ptr::null_mut();
    v___x_2993_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__63),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__63_once),
        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__63,
    );
    v___x_2994_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2994_, 0, v___x_2993_);
    return v___x_2994_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___redArg(
    mut v_e_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3005_: u8 = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: u8 = 0;
    let mut v_arg_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: u8 = 0;
    let mut v___y_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3025_: u8 = 0;
    let mut v___x_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3048_: u8 = 0;
    let mut v_a_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3052_: u8 = 0;
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3056_: u8 = 0;
    let mut v___y_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3065_: u8 = 0;
    let mut v___y_3066_: u8 = 0;
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_3083_: u8 = 0;
    let mut v___x_3084_: u8 = 0;
    let mut v___x_3085_: u8 = 0;
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3092_: u8 = 0;
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: u8 = 0;
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: u8 = 0;
    let mut v___x_3098_: u8 = 0;
    let mut v_arg_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3101_: u8 = 0;
    let mut v___x_3102_: u8 = 0;
    let mut v_arg_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3106_: u8 = 0;
    let mut v___x_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3108_: u8 = 0;
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3110_: u8 = 0;
    let mut v___x_3111_: u8 = 0;
    let mut v_arg_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3115_: u8 = 0;
    let mut v___x_3116_: u8 = 0;
    let mut v_arg_3117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3120_: u8 = 0;
    let mut v___x_3121_: u8 = 0;
    let mut v_arg_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3141_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    let mut v___x_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: u8 = 0;
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_a_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v___x_3182_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3187_: u8 = 0;
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: u8 = 0;
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: u8 = 0;
    let mut v___x_3193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3217_: u8 = 0;
    let mut v_a_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3221_: u8 = 0;
    let mut v___x_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3225_: u8 = 0;
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: u8 = 0;
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3270_: u8 = 0;
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3282_: u8 = 0;
    let mut v_a_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3286_: u8 = 0;
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3290_: u8 = 0;
    let mut v___x_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v_a_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3317_: u8 = 0;
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3321_: u8 = 0;
    let mut v_isSharedCheck_3322_: u8 = 0;
    let mut v_a_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v___x_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3330_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_2995_);
                v___x_3001_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2995_, v_a_2997_);
                if lean_obj_tag(v___x_3001_) == 0 {
                    v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
                    v_isSharedCheck_3322_ = (!lean_is_exclusive(v___x_3001_)) as u8;
                    if v_isSharedCheck_3322_ == 0 {
                        v___x_3004_ = v___x_3001_;
                        v_isShared_3005_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3002_);
                        lean_dec(v___x_3001_);
                        v___x_3004_ = lean_box(0);
                        v_isShared_3005_ = v_isSharedCheck_3322_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_2995_);
                    v_a_3323_ = lean_ctor_get(v___x_3001_, 0);
                    v_isSharedCheck_3330_ = (!lean_is_exclusive(v___x_3001_)) as u8;
                    if v_isSharedCheck_3330_ == 0 {
                        v___x_3325_ = v___x_3001_;
                        v_isShared_3326_ = v_isSharedCheck_3330_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_a_3323_);
                        lean_dec(v___x_3001_);
                        v___x_3325_ = lean_box(0);
                        v_isShared_3326_ = v_isSharedCheck_3330_;
                        state = 37;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3011_ = l_Lean_Expr_cleanupAnnotations(v_a_3002_);
                v___x_3012_ = l_Lean_Expr_isApp(v___x_3011_);
                if v___x_3012_ == 0 {
                    lean_dec_ref(v___x_3011_);
                    lean_dec_ref(v_e_2995_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3013_ = lean_ctor_get(v___x_3011_, 1);
                    lean_inc_ref(v_arg_3013_);
                    v___x_3014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3011_);
                    v___x_3015_ = l_Lean_Meta_Grind_pushNot___redArg___closed__1;
                    v___x_3016_ = l_Lean_Expr_isConstOf(v___x_3014_, v___x_3015_);
                    lean_dec_ref(v___x_3014_);
                    if v___x_3016_ == 0 {
                        lean_dec_ref(v_arg_3013_);
                        lean_dec_ref(v_e_2995_);
                        state = 2;
                        continue;
                    } else {
                        lean_del_object(v___x_3004_);
                        v___x_3088_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3013_, v_a_2997_);
                        if lean_obj_tag(v___x_3088_) == 0 {
                            v_a_3089_ = lean_ctor_get(v___x_3088_, 0);
                            v_isSharedCheck_3313_ = (!lean_is_exclusive(v___x_3088_)) as u8;
                            if v_isSharedCheck_3313_ == 0 {
                                v___x_3091_ = v___x_3088_;
                                v_isShared_3092_ = v_isSharedCheck_3313_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_3089_);
                                lean_dec(v___x_3088_);
                                v___x_3091_ = lean_box(0);
                                v_isShared_3092_ = v_isSharedCheck_3313_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_2995_);
                            v_a_3314_ = lean_ctor_get(v___x_3088_, 0);
                            v_isSharedCheck_3321_ = (!lean_is_exclusive(v___x_3088_)) as u8;
                            if v_isSharedCheck_3321_ == 0 {
                                v___x_3316_ = v___x_3088_;
                                v_isShared_3317_ = v_isSharedCheck_3321_;
                                state = 35;
                                continue;
                            } else {
                                lean_inc(v_a_3314_);
                                lean_dec(v___x_3088_);
                                v___x_3316_ = lean_box(0);
                                v_isShared_3317_ = v_isSharedCheck_3321_;
                                state = 35;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3007_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3005_ == 0 {
                    lean_ctor_set(v___x_3004_, 0, v___x_3007_);
                    v___x_3009_ = v___x_3004_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3010_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3010_, 0, v___x_3007_);
                    v___x_3009_ = v_reuseFailAlloc_3010_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3009_;
            }
            4 => {
                lean_inc_ref(v___y_3022_);
                lean_inc_ref_n(v___y_3023_, 3);
                lean_inc(v___y_3024_);
                v___x_3026_ = l_Lean_mkLambda(v___y_3024_, v___y_3025_, v___y_3023_, v___y_3022_);
                v___x_3027_ = l_Lean_mkNot(v___y_3022_);
                v___x_3028_ = l_Lean_mkLambda(v___y_3024_, v___y_3025_, v___y_3023_, v___x_3027_);
                v___x_3029_ = l_Lean_Meta_getLevel(
                    v___y_3023_,
                    v___y_3021_,
                    v___y_3020_,
                    v___y_3019_,
                    v___y_3018_,
                );
                if lean_obj_tag(v___x_3029_) == 0 {
                    v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3048_ = (!lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3048_ == 0 {
                        v___x_3032_ = v___x_3029_;
                        v_isShared_3033_ = v_isSharedCheck_3048_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3030_);
                        lean_dec(v___x_3029_);
                        v___x_3032_ = lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3048_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_3028_);
                    lean_dec_ref(v___x_3026_);
                    lean_dec_ref(v___y_3023_);
                    v_a_3049_ = lean_ctor_get(v___x_3029_, 0);
                    v_isSharedCheck_3056_ = (!lean_is_exclusive(v___x_3029_)) as u8;
                    if v_isSharedCheck_3056_ == 0 {
                        v___x_3051_ = v___x_3029_;
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3049_);
                        lean_dec(v___x_3029_);
                        v___x_3051_ = lean_box(0);
                        v_isShared_3052_ = v_isSharedCheck_3056_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3034_ = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
                v___x_3035_ = lean_box(0);
                v___x_3036_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3036_, 0, v_a_3030_);
                lean_ctor_set(v___x_3036_, 1, v___x_3035_);
                lean_inc_ref(v___x_3036_);
                v___x_3037_ = l_Lean_mkConst(v___x_3034_, v___x_3036_);
                lean_inc_ref(v___y_3023_);
                v___x_3038_ = l_Lean_mkAppB(v___x_3037_, v___y_3023_, v___x_3028_);
                v___x_3039_ = l_Lean_Meta_Grind_pushNot___redArg___closed__5;
                v___x_3040_ = l_Lean_mkConst(v___x_3039_, v___x_3036_);
                v___x_3041_ = l_Lean_mkAppB(v___x_3040_, v___y_3023_, v___x_3026_);
                v___x_3042_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3042_, 0, v___x_3041_);
                v___x_3043_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3043_, 0, v___x_3038_);
                lean_ctor_set(v___x_3043_, 1, v___x_3042_);
                lean_ctor_set_uint8(
                    v___x_3043_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3016_,
                );
                v___x_3044_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3044_, 0, v___x_3043_);
                if v_isShared_3033_ == 0 {
                    lean_ctor_set(v___x_3032_, 0, v___x_3044_);
                    v___x_3046_ = v___x_3032_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3047_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3047_, 0, v___x_3044_);
                    v___x_3046_ = v_reuseFailAlloc_3047_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3046_;
            }
            7 => {
                if v_isShared_3052_ == 0 {
                    v___x_3054_ = v___x_3051_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
                    v___x_3054_ = v_reuseFailAlloc_3055_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3054_;
            }
            9 => {
                if v___y_3066_ == 0 {
                    v___y_3018_ = v___y_3060_;
                    v___y_3019_ = v___y_3059_;
                    v___y_3020_ = v___y_3058_;
                    v___y_3021_ = v___y_3062_;
                    v___y_3022_ = v___y_3061_;
                    v___y_3023_ = v___y_3064_;
                    v___y_3024_ = v___y_3063_;
                    v___y_3025_ = v___y_3065_;
                    state = 4;
                    continue;
                } else {
                    lean_dec(v___y_3063_);
                    lean_inc_ref(v___y_3061_);
                    v___x_3067_ = l_Lean_mkNot(v___y_3061_);
                    lean_inc_ref(v___y_3064_);
                    v___x_3068_ = l_Lean_mkAnd(v___y_3064_, v___x_3067_);
                    v___x_3069_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__8),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__8_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__8,
                    );
                    v___x_3070_ = l_Lean_mkAppB(v___x_3069_, v___y_3064_, v___y_3061_);
                    v___x_3071_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3071_, 0, v___x_3070_);
                    v___x_3072_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3072_, 0, v___x_3068_);
                    lean_ctor_set(v___x_3072_, 1, v___x_3071_);
                    lean_ctor_set_uint8(
                        v___x_3072_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_3016_,
                    );
                    v___x_3073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3073_, 0, v___x_3072_);
                    v___x_3074_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3074_, 0, v___x_3073_);
                    return v___x_3074_;
                }
            }
            10 => {
                if lean_obj_tag(v_e_2995_) == 7 {
                    v_binderName_3080_ = lean_ctor_get(v_e_2995_, 0);
                    lean_inc(v_binderName_3080_);
                    v_binderType_3081_ = lean_ctor_get(v_e_2995_, 1);
                    lean_inc_ref(v_binderType_3081_);
                    v_body_3082_ = lean_ctor_get(v_e_2995_, 2);
                    lean_inc_ref(v_body_3082_);
                    v_binderInfo_3083_ = lean_ctor_get_uint8(
                        v_e_2995_,
                        (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    );
                    lean_dec_ref_known(v_e_2995_, 3);
                    v___x_3084_ = l_Lean_Expr_isProp(v_binderType_3081_);
                    if v___x_3084_ == 0 {
                        v___y_3058_ = v___y_3077_;
                        v___y_3059_ = v___y_3078_;
                        v___y_3060_ = v___y_3079_;
                        v___y_3061_ = v_body_3082_;
                        v___y_3062_ = v___y_3076_;
                        v___y_3063_ = v_binderName_3080_;
                        v___y_3064_ = v_binderType_3081_;
                        v___y_3065_ = v_binderInfo_3083_;
                        v___y_3066_ = v___x_3084_;
                        state = 9;
                        continue;
                    } else {
                        v___x_3085_ = l_Lean_Expr_hasLooseBVars(v_body_3082_);
                        if v___x_3085_ == 0 {
                            v___y_3058_ = v___y_3077_;
                            v___y_3059_ = v___y_3078_;
                            v___y_3060_ = v___y_3079_;
                            v___y_3061_ = v_body_3082_;
                            v___y_3062_ = v___y_3076_;
                            v___y_3063_ = v_binderName_3080_;
                            v___y_3064_ = v_binderType_3081_;
                            v___y_3065_ = v_binderInfo_3083_;
                            v___y_3066_ = v___x_3084_;
                            state = 9;
                            continue;
                        } else {
                            v___y_3018_ = v___y_3079_;
                            v___y_3019_ = v___y_3078_;
                            v___y_3020_ = v___y_3077_;
                            v___y_3021_ = v___y_3076_;
                            v___y_3022_ = v_body_3082_;
                            v___y_3023_ = v_binderType_3081_;
                            v___y_3024_ = v_binderName_3080_;
                            v___y_3025_ = v_binderInfo_3083_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_2995_);
                    v___x_3086_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    v___x_3087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3087_, 0, v___x_3086_);
                    return v___x_3087_;
                }
            }
            11 => {
                v___x_3093_ = l_Lean_Expr_cleanupAnnotations(v_a_3089_);
                v___x_3094_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
                v___x_3095_ = l_Lean_Expr_isConstOf(v___x_3093_, v___x_3094_);
                if v___x_3095_ == 0 {
                    v___x_3096_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
                    v___x_3097_ = l_Lean_Expr_isConstOf(v___x_3093_, v___x_3096_);
                    if v___x_3097_ == 0 {
                        v___x_3098_ = l_Lean_Expr_isApp(v___x_3093_);
                        if v___x_3098_ == 0 {
                            lean_dec_ref(v___x_3093_);
                            lean_del_object(v___x_3091_);
                            v___y_3076_ = v_a_2996_;
                            v___y_3077_ = v_a_2997_;
                            v___y_3078_ = v_a_2998_;
                            v___y_3079_ = v_a_2999_;
                            state = 10;
                            continue;
                        } else {
                            v_arg_3099_ = lean_ctor_get(v___x_3093_, 1);
                            lean_inc_ref(v_arg_3099_);
                            v___x_3100_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3093_);
                            v___x_3101_ = l_Lean_Expr_isConstOf(v___x_3100_, v___x_3015_);
                            if v___x_3101_ == 0 {
                                v___x_3102_ = l_Lean_Expr_isApp(v___x_3100_);
                                if v___x_3102_ == 0 {
                                    lean_dec_ref(v___x_3100_);
                                    lean_dec_ref(v_arg_3099_);
                                    lean_del_object(v___x_3091_);
                                    v___y_3076_ = v_a_2996_;
                                    v___y_3077_ = v_a_2997_;
                                    v___y_3078_ = v_a_2998_;
                                    v___y_3079_ = v_a_2999_;
                                    state = 10;
                                    continue;
                                } else {
                                    v_arg_3103_ = lean_ctor_get(v___x_3100_, 1);
                                    lean_inc_ref(v_arg_3103_);
                                    v___x_3104_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3100_);
                                    v___x_3105_ = l_Lean_Meta_Grind_pushNot___redArg___closed__3;
                                    v___x_3106_ = l_Lean_Expr_isConstOf(v___x_3104_, v___x_3105_);
                                    if v___x_3106_ == 0 {
                                        v___x_3107_ =
                                            l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                                        v___x_3108_ =
                                            l_Lean_Expr_isConstOf(v___x_3104_, v___x_3107_);
                                        if v___x_3108_ == 0 {
                                            v___x_3109_ =
                                                l_Lean_Meta_Grind_pushNot___redArg___closed__12;
                                            v___x_3110_ =
                                                l_Lean_Expr_isConstOf(v___x_3104_, v___x_3109_);
                                            if v___x_3110_ == 0 {
                                                v___x_3111_ = l_Lean_Expr_isApp(v___x_3104_);
                                                if v___x_3111_ == 0 {
                                                    lean_dec_ref(v___x_3104_);
                                                    lean_dec_ref(v_arg_3103_);
                                                    lean_dec_ref(v_arg_3099_);
                                                    lean_del_object(v___x_3091_);
                                                    v___y_3076_ = v_a_2996_;
                                                    v___y_3077_ = v_a_2997_;
                                                    v___y_3078_ = v_a_2998_;
                                                    v___y_3079_ = v_a_2999_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    v_arg_3112_ = lean_ctor_get(v___x_3104_, 1);
                                                    lean_inc_ref(v_arg_3112_);
                                                    v___x_3113_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_3104_,
                                                    );
                                                    v___x_3114_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                                                    v___x_3115_ = l_Lean_Expr_isConstOf(
                                                        v___x_3113_,
                                                        v___x_3114_,
                                                    );
                                                    if v___x_3115_ == 0 {
                                                        v___x_3116_ =
                                                            l_Lean_Expr_isApp(v___x_3113_);
                                                        if v___x_3116_ == 0 {
                                                            lean_dec_ref(v___x_3113_);
                                                            lean_dec_ref(v_arg_3112_);
                                                            lean_dec_ref(v_arg_3103_);
                                                            lean_dec_ref(v_arg_3099_);
                                                            lean_del_object(v___x_3091_);
                                                            v___y_3076_ = v_a_2996_;
                                                            v___y_3077_ = v_a_2997_;
                                                            v___y_3078_ = v_a_2998_;
                                                            v___y_3079_ = v_a_2999_;
                                                            state = 10;
                                                            continue;
                                                        } else {
                                                            v_arg_3117_ =
                                                                lean_ctor_get(v___x_3113_, 1);
                                                            lean_inc_ref(v_arg_3117_);
                                                            v___x_3118_ =
                                                                l_Lean_Expr_appFnCleanup___redArg(
                                                                    v___x_3113_,
                                                                );
                                                            v___x_3119_ = l_Lean_Meta_Grind_pushNot___redArg___closed__15;
                                                            v___x_3120_ = l_Lean_Expr_isConstOf(
                                                                v___x_3118_,
                                                                v___x_3119_,
                                                            );
                                                            if v___x_3120_ == 0 {
                                                                v___x_3121_ =
                                                                    l_Lean_Expr_isApp(v___x_3118_);
                                                                if v___x_3121_ == 0 {
                                                                    lean_dec_ref(v___x_3118_);
                                                                    lean_dec_ref(v_arg_3117_);
                                                                    lean_dec_ref(v_arg_3112_);
                                                                    lean_dec_ref(v_arg_3103_);
                                                                    lean_dec_ref(v_arg_3099_);
                                                                    lean_del_object(v___x_3091_);
                                                                    v___y_3076_ = v_a_2996_;
                                                                    v___y_3077_ = v_a_2997_;
                                                                    v___y_3078_ = v_a_2998_;
                                                                    v___y_3079_ = v_a_2999_;
                                                                    state = 10;
                                                                    continue;
                                                                } else {
                                                                    v_arg_3122_ = lean_ctor_get(
                                                                        v___x_3118_,
                                                                        1,
                                                                    );
                                                                    lean_inc_ref(v_arg_3122_);
                                                                    v___x_3123_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3118_);
                                                                    v___x_3124_ = l_Lean_Meta_Grind_simpDIte___redArg___closed__3;
                                                                    v___x_3125_ =
                                                                        l_Lean_Expr_isConstOf(
                                                                            v___x_3123_,
                                                                            v___x_3124_,
                                                                        );
                                                                    if v___x_3125_ == 0 {
                                                                        lean_dec_ref(v___x_3123_);
                                                                        lean_dec_ref(v_arg_3122_);
                                                                        lean_dec_ref(v_arg_3117_);
                                                                        lean_dec_ref(v_arg_3112_);
                                                                        lean_dec_ref(v_arg_3103_);
                                                                        lean_dec_ref(v_arg_3099_);
                                                                        lean_del_object(
                                                                            v___x_3091_,
                                                                        );
                                                                        v___y_3076_ = v_a_2996_;
                                                                        v___y_3077_ = v_a_2997_;
                                                                        v___y_3078_ = v_a_2998_;
                                                                        v___y_3079_ = v_a_2999_;
                                                                        state = 10;
                                                                        continue;
                                                                    } else {
                                                                        lean_dec_ref(v_e_2995_);
                                                                        lean_inc_ref(v_arg_3103_);
                                                                        v___x_3126_ = l_Lean_mkNot(
                                                                            v_arg_3103_,
                                                                        );
                                                                        lean_inc_ref(v_arg_3099_);
                                                                        v___x_3127_ = l_Lean_mkNot(
                                                                            v_arg_3099_,
                                                                        );
                                                                        lean_inc_ref(v_arg_3112_);
                                                                        lean_inc_ref(v_arg_3117_);
                                                                        v___x_3128_ = l_Lean_mkApp5(
                                                                            v___x_3123_,
                                                                            v_arg_3122_,
                                                                            v_arg_3117_,
                                                                            v_arg_3112_,
                                                                            v___x_3126_,
                                                                            v___x_3127_,
                                                                        );
                                                                        v___x_3129_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__18), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__18_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__18);
                                                                        v___x_3130_ = l_Lean_mkApp4(
                                                                            v___x_3129_,
                                                                            v_arg_3117_,
                                                                            v_arg_3112_,
                                                                            v_arg_3103_,
                                                                            v_arg_3099_,
                                                                        );
                                                                        v___x_3131_ =
                                                                            lean_alloc_ctor(
                                                                                1,
                                                                                1,
                                                                                (0) as u32,
                                                                            );
                                                                        lean_ctor_set(
                                                                            v___x_3131_,
                                                                            0,
                                                                            v___x_3130_,
                                                                        );
                                                                        v___x_3132_ =
                                                                            lean_alloc_ctor(
                                                                                0,
                                                                                2,
                                                                                (1) as u32,
                                                                            );
                                                                        lean_ctor_set(
                                                                            v___x_3132_,
                                                                            0,
                                                                            v___x_3128_,
                                                                        );
                                                                        lean_ctor_set(
                                                                            v___x_3132_,
                                                                            1,
                                                                            v___x_3131_,
                                                                        );
                                                                        lean_ctor_set_uint8(
                                                                            v___x_3132_,
                                                                            (core::mem::size_of::<
                                                                                *mut LeanObject,
                                                                            >(
                                                                            ) * 2)
                                                                                as u32,
                                                                            v___x_3125_,
                                                                        );
                                                                        v___x_3133_ =
                                                                            lean_alloc_ctor(
                                                                                1,
                                                                                1,
                                                                                (0) as u32,
                                                                            );
                                                                        lean_ctor_set(
                                                                            v___x_3133_,
                                                                            0,
                                                                            v___x_3132_,
                                                                        );
                                                                        if v_isShared_3092_ == 0 {
                                                                            lean_ctor_set(
                                                                                v___x_3091_,
                                                                                0,
                                                                                v___x_3133_,
                                                                            );
                                                                            v___x_3135_ =
                                                                                v___x_3091_;
                                                                            state = 12;
                                                                            continue;
                                                                        } else {
                                                                            v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, (0) as u32);
                                                                            lean_ctor_set(v_reuseFailAlloc_3136_, 0, v___x_3133_);
                                                                            v___x_3135_ = v_reuseFailAlloc_3136_;
                                                                            state = 12;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_3118_);
                                                                lean_dec_ref(v_arg_3112_);
                                                                lean_del_object(v___x_3091_);
                                                                lean_dec_ref(v_e_2995_);
                                                                v___x_3137_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3117_, v_a_2997_);
                                                                if lean_obj_tag(v___x_3137_) == 0 {
                                                                    v_a_3138_ = lean_ctor_get(
                                                                        v___x_3137_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_3173_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_3137_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_3173_ == 0 {
                                                                        v___x_3140_ = v___x_3137_;
                                                                        v_isShared_3141_ =
                                                                            v_isSharedCheck_3173_;
                                                                        state = 13;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_3138_);
                                                                        lean_dec(v___x_3137_);
                                                                        v___x_3140_ = lean_box(0);
                                                                        v_isShared_3141_ =
                                                                            v_isSharedCheck_3173_;
                                                                        state = 13;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec_ref(v_arg_3103_);
                                                                    lean_dec_ref(v_arg_3099_);
                                                                    v_a_3174_ = lean_ctor_get(
                                                                        v___x_3137_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_3181_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_3137_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_3181_ == 0 {
                                                                        v___x_3176_ = v___x_3137_;
                                                                        v_isShared_3177_ =
                                                                            v_isSharedCheck_3181_;
                                                                        state = 17;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_3174_);
                                                                        lean_dec(v___x_3137_);
                                                                        v___x_3176_ = lean_box(0);
                                                                        v_isShared_3177_ =
                                                                            v_isSharedCheck_3181_;
                                                                        state = 17;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec_ref(v_e_2995_);
                                                        v___x_3182_ =
                                                            l_Lean_Expr_isProp(v_arg_3112_);
                                                        if v___x_3182_ == 0 {
                                                            lean_del_object(v___x_3091_);
                                                            v___x_3183_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3099_, v_a_2997_);
                                                            if lean_obj_tag(v___x_3183_) == 0 {
                                                                v_a_3184_ =
                                                                    lean_ctor_get(v___x_3183_, 0);
                                                                v_isSharedCheck_3217_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3183_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3217_ == 0 {
                                                                    v___x_3186_ = v___x_3183_;
                                                                    v_isShared_3187_ =
                                                                        v_isSharedCheck_3217_;
                                                                    state = 19;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3184_);
                                                                    lean_dec(v___x_3183_);
                                                                    v___x_3186_ = lean_box(0);
                                                                    v_isShared_3187_ =
                                                                        v_isSharedCheck_3217_;
                                                                    state = 19;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v___x_3113_);
                                                                lean_dec_ref(v_arg_3112_);
                                                                lean_dec_ref(v_arg_3103_);
                                                                v_a_3218_ =
                                                                    lean_ctor_get(v___x_3183_, 0);
                                                                v_isSharedCheck_3225_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_3183_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_3225_ == 0 {
                                                                    v___x_3220_ = v___x_3183_;
                                                                    v_isShared_3221_ =
                                                                        v_isSharedCheck_3225_;
                                                                    state = 23;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_3218_);
                                                                    lean_dec(v___x_3183_);
                                                                    v___x_3220_ = lean_box(0);
                                                                    v_isShared_3221_ =
                                                                        v_isSharedCheck_3225_;
                                                                    state = 23;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_inc_ref(v_arg_3099_);
                                                            v___x_3226_ = l_Lean_mkNot(v_arg_3099_);
                                                            lean_inc_ref(v_arg_3103_);
                                                            v___x_3227_ = l_Lean_mkApp3(
                                                                v___x_3113_,
                                                                v_arg_3112_,
                                                                v_arg_3103_,
                                                                v___x_3226_,
                                                            );
                                                            v___x_3228_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__40), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__40_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__40);
                                                            v___x_3229_ = l_Lean_mkAppB(
                                                                v___x_3228_,
                                                                v_arg_3103_,
                                                                v_arg_3099_,
                                                            );
                                                            v___x_3230_ =
                                                                lean_alloc_ctor(1, 1, (0) as u32);
                                                            lean_ctor_set(
                                                                v___x_3230_,
                                                                0,
                                                                v___x_3229_,
                                                            );
                                                            v___x_3231_ =
                                                                lean_alloc_ctor(0, 2, (1) as u32);
                                                            lean_ctor_set(
                                                                v___x_3231_,
                                                                0,
                                                                v___x_3227_,
                                                            );
                                                            lean_ctor_set(
                                                                v___x_3231_,
                                                                1,
                                                                v___x_3230_,
                                                            );
                                                            lean_ctor_set_uint8(
                                                                v___x_3231_,
                                                                (core::mem::size_of::<
                                                                    *mut LeanObject,
                                                                >(
                                                                ) * 2)
                                                                    as u32,
                                                                v___x_3115_,
                                                            );
                                                            v___x_3232_ =
                                                                lean_alloc_ctor(1, 1, (0) as u32);
                                                            lean_ctor_set(
                                                                v___x_3232_,
                                                                0,
                                                                v___x_3231_,
                                                            );
                                                            if v_isShared_3092_ == 0 {
                                                                lean_ctor_set(
                                                                    v___x_3091_,
                                                                    0,
                                                                    v___x_3232_,
                                                                );
                                                                v___x_3234_ = v___x_3091_;
                                                                state = 25;
                                                                continue;
                                                            } else {
                                                                v_reuseFailAlloc_3235_ =
                                                                    lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                lean_ctor_set(
                                                                    v_reuseFailAlloc_3235_,
                                                                    0,
                                                                    v___x_3232_,
                                                                );
                                                                v___x_3234_ =
                                                                    v_reuseFailAlloc_3235_;
                                                                state = 25;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v___x_3104_);
                                                lean_dec_ref(v_e_2995_);
                                                v___x_3236_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__41), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__41_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__41);
                                                lean_inc_ref(v_arg_3103_);
                                                v___x_3237_ = l_Lean_mkNot(v_arg_3103_);
                                                lean_inc_ref(v_arg_3099_);
                                                v___x_3238_ = l_Lean_mkNot(v_arg_3099_);
                                                v___x_3239_ = l_Lean_mkAppB(
                                                    v___x_3236_,
                                                    v___x_3237_,
                                                    v___x_3238_,
                                                );
                                                v___x_3240_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__44), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__44_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__44);
                                                v___x_3241_ = l_Lean_mkAppB(
                                                    v___x_3240_,
                                                    v_arg_3103_,
                                                    v_arg_3099_,
                                                );
                                                v___x_3242_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_3242_, 0, v___x_3241_);
                                                v___x_3243_ = lean_alloc_ctor(0, 2, (1) as u32);
                                                lean_ctor_set(v___x_3243_, 0, v___x_3239_);
                                                lean_ctor_set(v___x_3243_, 1, v___x_3242_);
                                                lean_ctor_set_uint8(
                                                    v___x_3243_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 2)
                                                        as u32,
                                                    v___x_3110_,
                                                );
                                                v___x_3244_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_3244_, 0, v___x_3243_);
                                                if v_isShared_3092_ == 0 {
                                                    lean_ctor_set(v___x_3091_, 0, v___x_3244_);
                                                    v___x_3246_ = v___x_3091_;
                                                    state = 26;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3247_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_3247_,
                                                        0,
                                                        v___x_3244_,
                                                    );
                                                    v___x_3246_ = v_reuseFailAlloc_3247_;
                                                    state = 26;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___x_3104_);
                                            lean_dec_ref(v_e_2995_);
                                            v___x_3248_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__45), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__45_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__45);
                                            lean_inc_ref(v_arg_3103_);
                                            v___x_3249_ = l_Lean_mkNot(v_arg_3103_);
                                            lean_inc_ref(v_arg_3099_);
                                            v___x_3250_ = l_Lean_mkNot(v_arg_3099_);
                                            v___x_3251_ = l_Lean_mkAppB(
                                                v___x_3248_,
                                                v___x_3249_,
                                                v___x_3250_,
                                            );
                                            v___x_3252_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__48), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__48_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__48);
                                            v___x_3253_ = l_Lean_mkAppB(
                                                v___x_3252_,
                                                v_arg_3103_,
                                                v_arg_3099_,
                                            );
                                            v___x_3254_ = lean_alloc_ctor(1, 1, (0) as u32);
                                            lean_ctor_set(v___x_3254_, 0, v___x_3253_);
                                            v___x_3255_ = lean_alloc_ctor(0, 2, (1) as u32);
                                            lean_ctor_set(v___x_3255_, 0, v___x_3251_);
                                            lean_ctor_set(v___x_3255_, 1, v___x_3254_);
                                            lean_ctor_set_uint8(
                                                v___x_3255_,
                                                (core::mem::size_of::<*mut LeanObject>() * 2)
                                                    as u32,
                                                v___x_3108_,
                                            );
                                            v___x_3256_ = lean_alloc_ctor(1, 1, (0) as u32);
                                            lean_ctor_set(v___x_3256_, 0, v___x_3255_);
                                            if v_isShared_3092_ == 0 {
                                                lean_ctor_set(v___x_3091_, 0, v___x_3256_);
                                                v___x_3258_ = v___x_3091_;
                                                state = 27;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3259_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_3259_,
                                                    0,
                                                    v___x_3256_,
                                                );
                                                v___x_3258_ = v_reuseFailAlloc_3259_;
                                                state = 27;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___x_3104_);
                                        lean_del_object(v___x_3091_);
                                        lean_dec_ref(v_e_2995_);
                                        v___x_3260_ =
                                            l_Lean_Meta_Grind_pushNot___redArg___closed__50;
                                        v___x_3261_ = 0;
                                        v___x_3262_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__51), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__51_once), _init_l_Lean_Meta_Grind_pushNot___redArg___closed__51);
                                        lean_inc_ref(v_arg_3099_);
                                        v___x_3263_ =
                                            l_Lean_Expr_app___override(v_arg_3099_, v___x_3262_);
                                        v___x_3264_ = l_Lean_mkNot(v___x_3263_);
                                        lean_inc_ref_n(v_arg_3103_, 2);
                                        v___x_3265_ = l_Lean_mkForall(
                                            v___x_3260_,
                                            v___x_3261_,
                                            v_arg_3103_,
                                            v___x_3264_,
                                        );
                                        v___x_3266_ = l_Lean_Meta_getLevel(
                                            v_arg_3103_,
                                            v_a_2996_,
                                            v_a_2997_,
                                            v_a_2998_,
                                            v_a_2999_,
                                        );
                                        if lean_obj_tag(v___x_3266_) == 0 {
                                            v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                                            v_isSharedCheck_3282_ =
                                                (!lean_is_exclusive(v___x_3266_)) as u8;
                                            if v_isSharedCheck_3282_ == 0 {
                                                v___x_3269_ = v___x_3266_;
                                                v_isShared_3270_ = v_isSharedCheck_3282_;
                                                state = 28;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3267_);
                                                lean_dec(v___x_3266_);
                                                v___x_3269_ = lean_box(0);
                                                v_isShared_3270_ = v_isSharedCheck_3282_;
                                                state = 28;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref(v___x_3265_);
                                            lean_dec_ref(v_arg_3103_);
                                            lean_dec_ref(v_arg_3099_);
                                            v_a_3283_ = lean_ctor_get(v___x_3266_, 0);
                                            v_isSharedCheck_3290_ =
                                                (!lean_is_exclusive(v___x_3266_)) as u8;
                                            if v_isSharedCheck_3290_ == 0 {
                                                v___x_3285_ = v___x_3266_;
                                                v_isShared_3286_ = v_isSharedCheck_3290_;
                                                state = 30;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3283_);
                                                lean_dec(v___x_3266_);
                                                v___x_3285_ = lean_box(0);
                                                v_isShared_3286_ = v_isSharedCheck_3290_;
                                                state = 30;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_3100_);
                                lean_dec_ref(v_e_2995_);
                                v___x_3291_ = lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_pushNot___redArg___closed__56
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Meta_Grind_pushNot___redArg___closed__56_once
                                    ),
                                    _init_l_Lean_Meta_Grind_pushNot___redArg___closed__56,
                                );
                                lean_inc_ref(v_arg_3099_);
                                v___x_3292_ = l_Lean_Expr_app___override(v___x_3291_, v_arg_3099_);
                                v___x_3293_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3293_, 0, v___x_3292_);
                                v___x_3294_ = lean_alloc_ctor(0, 2, (1) as u32);
                                lean_ctor_set(v___x_3294_, 0, v_arg_3099_);
                                lean_ctor_set(v___x_3294_, 1, v___x_3293_);
                                lean_ctor_set_uint8(
                                    v___x_3294_,
                                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                    v___x_3101_,
                                );
                                v___x_3295_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_3295_, 0, v___x_3294_);
                                if v_isShared_3092_ == 0 {
                                    lean_ctor_set(v___x_3091_, 0, v___x_3295_);
                                    v___x_3297_ = v___x_3091_;
                                    state = 32;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3298_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3295_);
                                    v___x_3297_ = v_reuseFailAlloc_3298_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3093_);
                        lean_dec_ref(v_e_2995_);
                        v___x_3299_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpEq___redArg___closed__9_once
                            ),
                            _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                        );
                        v___x_3300_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__60
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__60_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__60,
                        );
                        v___x_3301_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_3301_, 0, v___x_3299_);
                        lean_ctor_set(v___x_3301_, 1, v___x_3300_);
                        lean_ctor_set_uint8(
                            v___x_3301_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_3097_,
                        );
                        v___x_3302_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3302_, 0, v___x_3301_);
                        if v_isShared_3092_ == 0 {
                            lean_ctor_set(v___x_3091_, 0, v___x_3302_);
                            v___x_3304_ = v___x_3091_;
                            state = 33;
                            continue;
                        } else {
                            v_reuseFailAlloc_3305_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3305_, 0, v___x_3302_);
                            v___x_3304_ = v_reuseFailAlloc_3305_;
                            state = 33;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3093_);
                    lean_dec_ref(v_e_2995_);
                    v___x_3306_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__6_once),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__6,
                    );
                    v___x_3307_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__64),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__64_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__64,
                    );
                    v___x_3308_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3308_, 0, v___x_3306_);
                    lean_ctor_set(v___x_3308_, 1, v___x_3307_);
                    lean_ctor_set_uint8(
                        v___x_3308_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_3095_,
                    );
                    v___x_3309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3309_, 0, v___x_3308_);
                    if v_isShared_3092_ == 0 {
                        lean_ctor_set(v___x_3091_, 0, v___x_3309_);
                        v___x_3311_ = v___x_3091_;
                        state = 34;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3312_, 0, v___x_3309_);
                        v___x_3311_ = v_reuseFailAlloc_3312_;
                        state = 34;
                        continue;
                    }
                }
            }
            12 => {
                return v___x_3135_;
            }
            13 => {
                v___x_3142_ = l_Lean_Expr_cleanupAnnotations(v_a_3138_);
                v___x_3143_ = l_Lean_Meta_Grind_pushNot___redArg___closed__20;
                v___x_3144_ = l_Lean_Expr_isConstOf(v___x_3142_, v___x_3143_);
                if v___x_3144_ == 0 {
                    v___x_3145_ = l_Lean_Meta_Grind_pushNot___redArg___closed__22;
                    v___x_3146_ = l_Lean_Expr_isConstOf(v___x_3142_, v___x_3145_);
                    lean_dec_ref(v___x_3142_);
                    if v___x_3146_ == 0 {
                        lean_dec_ref(v_arg_3103_);
                        lean_dec_ref(v_arg_3099_);
                        v___x_3147_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_3141_ == 0 {
                            lean_ctor_set(v___x_3140_, 0, v___x_3147_);
                            v___x_3149_ = v___x_3140_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3147_);
                            v___x_3149_ = v_reuseFailAlloc_3150_;
                            state = 14;
                            continue;
                        }
                    } else {
                        v___x_3151_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__24
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__24_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__24,
                        );
                        lean_inc_ref(v_arg_3099_);
                        v___x_3152_ = l_Lean_mkIntAdd(v_arg_3099_, v___x_3151_);
                        lean_inc_ref(v_arg_3103_);
                        v___x_3153_ = l_Lean_mkIntLE(v___x_3152_, v_arg_3103_);
                        v___x_3154_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__27
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__27_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__27,
                        );
                        v___x_3155_ = l_Lean_mkAppB(v___x_3154_, v_arg_3103_, v_arg_3099_);
                        v___x_3156_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3156_, 0, v___x_3155_);
                        v___x_3157_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_3157_, 0, v___x_3153_);
                        lean_ctor_set(v___x_3157_, 1, v___x_3156_);
                        lean_ctor_set_uint8(
                            v___x_3157_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_3146_,
                        );
                        v___x_3158_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3158_, 0, v___x_3157_);
                        if v_isShared_3141_ == 0 {
                            lean_ctor_set(v___x_3140_, 0, v___x_3158_);
                            v___x_3160_ = v___x_3140_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3158_);
                            v___x_3160_ = v_reuseFailAlloc_3161_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3142_);
                    v___x_3162_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__28),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__28_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__28,
                    );
                    lean_inc_ref(v_arg_3099_);
                    v___x_3163_ = l_Lean_mkNatAdd(v_arg_3099_, v___x_3162_);
                    lean_inc_ref(v_arg_3103_);
                    v___x_3164_ = l_Lean_mkNatLE(v___x_3163_, v_arg_3103_);
                    v___x_3165_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__30),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__30_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__30,
                    );
                    v___x_3166_ = l_Lean_mkAppB(v___x_3165_, v_arg_3103_, v_arg_3099_);
                    v___x_3167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3167_, 0, v___x_3166_);
                    v___x_3168_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3168_, 0, v___x_3164_);
                    lean_ctor_set(v___x_3168_, 1, v___x_3167_);
                    lean_ctor_set_uint8(
                        v___x_3168_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_3144_,
                    );
                    v___x_3169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3169_, 0, v___x_3168_);
                    if v_isShared_3141_ == 0 {
                        lean_ctor_set(v___x_3140_, 0, v___x_3169_);
                        v___x_3171_ = v___x_3140_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
                        v___x_3171_ = v_reuseFailAlloc_3172_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                return v___x_3149_;
            }
            15 => {
                return v___x_3160_;
            }
            16 => {
                return v___x_3171_;
            }
            17 => {
                if v_isShared_3177_ == 0 {
                    v___x_3179_ = v___x_3176_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
                    v___x_3179_ = v_reuseFailAlloc_3180_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3179_;
            }
            19 => {
                v___x_3188_ = l_Lean_Expr_cleanupAnnotations(v_a_3184_);
                v___x_3189_ = l_Lean_Meta_Grind_simpEq___redArg___closed__30;
                v___x_3190_ = l_Lean_Expr_isConstOf(v___x_3188_, v___x_3189_);
                if v___x_3190_ == 0 {
                    v___x_3191_ = l_Lean_Meta_Grind_simpEq___redArg___closed__21;
                    v___x_3192_ = l_Lean_Expr_isConstOf(v___x_3188_, v___x_3191_);
                    lean_dec_ref(v___x_3188_);
                    if v___x_3192_ == 0 {
                        lean_dec_ref(v___x_3113_);
                        lean_dec_ref(v_arg_3112_);
                        lean_dec_ref(v_arg_3103_);
                        v___x_3193_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                        if v_isShared_3187_ == 0 {
                            lean_ctor_set(v___x_3186_, 0, v___x_3193_);
                            v___x_3195_ = v___x_3186_;
                            state = 20;
                            continue;
                        } else {
                            v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3193_);
                            v___x_3195_ = v_reuseFailAlloc_3196_;
                            state = 20;
                            continue;
                        }
                    } else {
                        v___x_3197_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__31
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__31_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__31,
                        );
                        lean_inc_ref(v_arg_3103_);
                        v___x_3198_ =
                            l_Lean_mkApp3(v___x_3113_, v_arg_3112_, v_arg_3103_, v___x_3197_);
                        v___x_3199_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__34
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_pushNot___redArg___closed__34_once
                            ),
                            _init_l_Lean_Meta_Grind_pushNot___redArg___closed__34,
                        );
                        v___x_3200_ = l_Lean_Expr_app___override(v___x_3199_, v_arg_3103_);
                        v___x_3201_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3201_, 0, v___x_3200_);
                        v___x_3202_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_3202_, 0, v___x_3198_);
                        lean_ctor_set(v___x_3202_, 1, v___x_3201_);
                        lean_ctor_set_uint8(
                            v___x_3202_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_3115_,
                        );
                        v___x_3203_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3203_, 0, v___x_3202_);
                        if v_isShared_3187_ == 0 {
                            lean_ctor_set(v___x_3186_, 0, v___x_3203_);
                            v___x_3205_ = v___x_3186_;
                            state = 21;
                            continue;
                        } else {
                            v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3203_);
                            v___x_3205_ = v_reuseFailAlloc_3206_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3188_);
                    v___x_3207_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__22),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpEq___redArg___closed__22_once
                        ),
                        _init_l_Lean_Meta_Grind_simpEq___redArg___closed__22,
                    );
                    lean_inc_ref(v_arg_3103_);
                    v___x_3208_ = l_Lean_mkApp3(v___x_3113_, v_arg_3112_, v_arg_3103_, v___x_3207_);
                    v___x_3209_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_pushNot___redArg___closed__37),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_pushNot___redArg___closed__37_once
                        ),
                        _init_l_Lean_Meta_Grind_pushNot___redArg___closed__37,
                    );
                    v___x_3210_ = l_Lean_Expr_app___override(v___x_3209_, v_arg_3103_);
                    v___x_3211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3211_, 0, v___x_3210_);
                    v___x_3212_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3212_, 0, v___x_3208_);
                    lean_ctor_set(v___x_3212_, 1, v___x_3211_);
                    lean_ctor_set_uint8(
                        v___x_3212_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_3115_,
                    );
                    v___x_3213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3213_, 0, v___x_3212_);
                    if v_isShared_3187_ == 0 {
                        lean_ctor_set(v___x_3186_, 0, v___x_3213_);
                        v___x_3215_ = v___x_3186_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3216_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3216_, 0, v___x_3213_);
                        v___x_3215_ = v_reuseFailAlloc_3216_;
                        state = 22;
                        continue;
                    }
                }
            }
            20 => {
                return v___x_3195_;
            }
            21 => {
                return v___x_3205_;
            }
            22 => {
                return v___x_3215_;
            }
            23 => {
                if v_isShared_3221_ == 0 {
                    v___x_3223_ = v___x_3220_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
                    v___x_3223_ = v_reuseFailAlloc_3224_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3223_;
            }
            25 => {
                return v___x_3234_;
            }
            26 => {
                return v___x_3246_;
            }
            27 => {
                return v___x_3258_;
            }
            28 => {
                v___x_3271_ = l_Lean_Meta_Grind_pushNot___redArg___closed__53;
                v___x_3272_ = lean_box(0);
                v___x_3273_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3273_, 0, v_a_3267_);
                lean_ctor_set(v___x_3273_, 1, v___x_3272_);
                v___x_3274_ = l_Lean_mkConst(v___x_3271_, v___x_3273_);
                v___x_3275_ = l_Lean_mkAppB(v___x_3274_, v_arg_3103_, v_arg_3099_);
                v___x_3276_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3276_, 0, v___x_3275_);
                v___x_3277_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3277_, 0, v___x_3265_);
                lean_ctor_set(v___x_3277_, 1, v___x_3276_);
                lean_ctor_set_uint8(
                    v___x_3277_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3106_,
                );
                v___x_3278_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3278_, 0, v___x_3277_);
                if v_isShared_3270_ == 0 {
                    lean_ctor_set(v___x_3269_, 0, v___x_3278_);
                    v___x_3280_ = v___x_3269_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3281_, 0, v___x_3278_);
                    v___x_3280_ = v_reuseFailAlloc_3281_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_3280_;
            }
            30 => {
                if v_isShared_3286_ == 0 {
                    v___x_3288_ = v___x_3285_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
                    v___x_3288_ = v_reuseFailAlloc_3289_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3288_;
            }
            32 => {
                return v___x_3297_;
            }
            33 => {
                return v___x_3304_;
            }
            34 => {
                return v___x_3311_;
            }
            35 => {
                if v_isShared_3317_ == 0 {
                    v___x_3319_ = v___x_3316_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3320_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_a_3314_);
                    v___x_3319_ = v_reuseFailAlloc_3320_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_3319_;
            }
            37 => {
                if v_isShared_3326_ == 0 {
                    v___x_3328_ = v___x_3325_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_3329_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3329_, 0, v_a_3323_);
                    v___x_3328_ = v_reuseFailAlloc_3329_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_3328_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___redArg___boxed(
    mut v_e_3331_: *mut LeanObject,
    mut v_a_3332_: *mut LeanObject,
    mut v_a_3333_: *mut LeanObject,
    mut v_a_3334_: *mut LeanObject,
    mut v_a_3335_: *mut LeanObject,
    mut v_a_3336_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3337_: *mut LeanObject = core::ptr::null_mut();
    v_res_3337_ =
        l_Lean_Meta_Grind_pushNot___redArg(v_e_3331_, v_a_3332_, v_a_3333_, v_a_3334_, v_a_3335_);
    lean_dec(v_a_3335_);
    lean_dec_ref(v_a_3334_);
    lean_dec(v_a_3333_);
    lean_dec_ref(v_a_3332_);
    return v_res_3337_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot(
    mut v_e_3338_: *mut LeanObject,
    mut v_a_3339_: *mut LeanObject,
    mut v_a_3340_: *mut LeanObject,
    mut v_a_3341_: *mut LeanObject,
    mut v_a_3342_: *mut LeanObject,
    mut v_a_3343_: *mut LeanObject,
    mut v_a_3344_: *mut LeanObject,
    mut v_a_3345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    v___x_3347_ =
        l_Lean_Meta_Grind_pushNot___redArg(v_e_3338_, v_a_3342_, v_a_3343_, v_a_3344_, v_a_3345_);
    return v___x_3347_;
}
pub unsafe fn l_Lean_Meta_Grind_pushNot___boxed(
    mut v_e_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
    mut v_a_3350_: *mut LeanObject,
    mut v_a_3351_: *mut LeanObject,
    mut v_a_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3357_: *mut LeanObject = core::ptr::null_mut();
    v_res_3357_ = l_Lean_Meta_Grind_pushNot(
        v_e_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_,
    );
    lean_dec(v_a_3355_);
    lean_dec_ref(v_a_3354_);
    lean_dec(v_a_3353_);
    lean_dec_ref(v_a_3352_);
    lean_dec(v_a_3351_);
    lean_dec_ref(v_a_3350_);
    lean_dec(v_a_3349_);
    return v_res_3357_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_()
-> *mut LeanObject {
    let mut v___x_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    v___x_3374_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
    v___x_3375_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
    v___x_3376_ = lean_alloc_closure(
        l_Lean_Meta_Grind_pushNot___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3377_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3374_, v___x_3375_, v___x_3376_);
    return v___x_3377_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10____boxed(
    mut v_a_3378_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3379_: *mut LeanObject = core::ptr::null_mut();
    v_res_3379_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_();
    return v_res_3379_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2() -> *mut LeanObject {
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    v___x_3385_ = lean_box(0);
    v___x_3386_ = l_Lean_Meta_Grind_simpOr___redArg___closed__1;
    v___x_3387_ = l_Lean_mkConst(v___x_3386_, v___x_3385_);
    return v___x_3387_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5() -> *mut LeanObject {
    let mut v___x_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    v___x_3393_ = lean_box(0);
    v___x_3394_ = l_Lean_Meta_Grind_simpOr___redArg___closed__4;
    v___x_3395_ = l_Lean_mkConst(v___x_3394_, v___x_3393_);
    return v___x_3395_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8() -> *mut LeanObject {
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: *mut LeanObject = core::ptr::null_mut();
    v___x_3399_ = lean_box(0);
    v___x_3400_ = l_Lean_Meta_Grind_simpOr___redArg___closed__7;
    v___x_3401_ = l_Lean_mkConst(v___x_3400_, v___x_3399_);
    return v___x_3401_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11() -> *mut LeanObject {
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3407_: *mut LeanObject = core::ptr::null_mut();
    v___x_3405_ = lean_box(0);
    v___x_3406_ = l_Lean_Meta_Grind_simpOr___redArg___closed__10;
    v___x_3407_ = l_Lean_mkConst(v___x_3406_, v___x_3405_);
    return v___x_3407_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14() -> *mut LeanObject {
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    v___x_3413_ = lean_box(0);
    v___x_3414_ = l_Lean_Meta_Grind_simpOr___redArg___closed__13;
    v___x_3415_ = l_Lean_mkConst(v___x_3414_, v___x_3413_);
    return v___x_3415_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17() -> *mut LeanObject {
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3421_: *mut LeanObject = core::ptr::null_mut();
    v___x_3419_ = lean_box(0);
    v___x_3420_ = l_Lean_Meta_Grind_simpOr___redArg___closed__16;
    v___x_3421_ = l_Lean_mkConst(v___x_3420_, v___x_3419_);
    return v___x_3421_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20() -> *mut LeanObject {
    let mut v___x_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3427_: *mut LeanObject = core::ptr::null_mut();
    v___x_3425_ = lean_box(0);
    v___x_3426_ = l_Lean_Meta_Grind_simpOr___redArg___closed__19;
    v___x_3427_ = l_Lean_mkConst(v___x_3426_, v___x_3425_);
    return v___x_3427_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___redArg(
    mut v_e_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3438_: u8 = 0;
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: u8 = 0;
    let mut v_arg_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v_arg_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3456_: u8 = 0;
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: u8 = 0;
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: u8 = 0;
    let mut v___x_3462_: u8 = 0;
    let mut v_arg_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: u8 = 0;
    let mut v_arg_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3469_: u8 = 0;
    let mut v___x_3470_: u8 = 0;
    let mut v___x_3471_: u8 = 0;
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_a_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v___x_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3528_: u8 = 0;
    let mut v___x_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3533_: u8 = 0;
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: u8 = 0;
    let mut v___x_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3538_: u8 = 0;
    let mut v___x_3539_: u8 = 0;
    let mut v_arg_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: u8 = 0;
    let mut v_arg_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_a_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v_a_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3585_: u8 = 0;
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3434_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3428_, v_a_3429_);
                if lean_obj_tag(v___x_3434_) == 0 {
                    v_a_3435_ = lean_ctor_get(v___x_3434_, 0);
                    v_isSharedCheck_3581_ = (!lean_is_exclusive(v___x_3434_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3437_ = v___x_3434_;
                        v_isShared_3438_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3435_);
                        lean_dec(v___x_3434_);
                        v___x_3437_ = lean_box(0);
                        v_isShared_3438_ = v_isSharedCheck_3581_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_3582_ = lean_ctor_get(v___x_3434_, 0);
                    v_isSharedCheck_3589_ = (!lean_is_exclusive(v___x_3434_)) as u8;
                    if v_isSharedCheck_3589_ == 0 {
                        v___x_3584_ = v___x_3434_;
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3582_);
                        lean_dec(v___x_3434_);
                        v___x_3584_ = lean_box(0);
                        v_isShared_3585_ = v_isSharedCheck_3589_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3432_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                v___x_3433_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3433_, 0, v___x_3432_);
                return v___x_3433_;
            }
            2 => {
                v___x_3444_ = l_Lean_Expr_cleanupAnnotations(v_a_3435_);
                v___x_3445_ = l_Lean_Expr_isApp(v___x_3444_);
                if v___x_3445_ == 0 {
                    lean_dec_ref(v___x_3444_);
                    state = 3;
                    continue;
                } else {
                    v_arg_3446_ = lean_ctor_get(v___x_3444_, 1);
                    lean_inc_ref(v_arg_3446_);
                    v___x_3447_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3444_);
                    v___x_3448_ = l_Lean_Expr_isApp(v___x_3447_);
                    if v___x_3448_ == 0 {
                        lean_dec_ref(v___x_3447_);
                        lean_dec_ref(v_arg_3446_);
                        state = 3;
                        continue;
                    } else {
                        v_arg_3449_ = lean_ctor_get(v___x_3447_, 1);
                        lean_inc_ref(v_arg_3449_);
                        v___x_3526_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3447_);
                        v___x_3527_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                        v___x_3528_ = l_Lean_Expr_isConstOf(v___x_3526_, v___x_3527_);
                        lean_dec_ref(v___x_3526_);
                        if v___x_3528_ == 0 {
                            lean_dec_ref(v_arg_3449_);
                            lean_dec_ref(v_arg_3446_);
                            state = 3;
                            continue;
                        } else {
                            lean_del_object(v___x_3437_);
                            lean_inc_ref(v_arg_3449_);
                            v___x_3529_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(
                                v_arg_3449_,
                                v_a_3429_,
                            );
                            if lean_obj_tag(v___x_3529_) == 0 {
                                v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
                                v_isSharedCheck_3572_ = (!lean_is_exclusive(v___x_3529_)) as u8;
                                if v_isSharedCheck_3572_ == 0 {
                                    v___x_3532_ = v___x_3529_;
                                    v_isShared_3533_ = v_isSharedCheck_3572_;
                                    state = 15;
                                    continue;
                                } else {
                                    lean_inc(v_a_3530_);
                                    lean_dec(v___x_3529_);
                                    v___x_3532_ = lean_box(0);
                                    v_isShared_3533_ = v_isSharedCheck_3572_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_arg_3449_);
                                lean_dec_ref(v_arg_3446_);
                                v_a_3573_ = lean_ctor_get(v___x_3529_, 0);
                                v_isSharedCheck_3580_ = (!lean_is_exclusive(v___x_3529_)) as u8;
                                if v_isSharedCheck_3580_ == 0 {
                                    v___x_3575_ = v___x_3529_;
                                    v_isShared_3576_ = v_isSharedCheck_3580_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_3573_);
                                    lean_dec(v___x_3529_);
                                    v___x_3575_ = lean_box(0);
                                    v_isShared_3576_ = v_isSharedCheck_3580_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            3 => {
                v___x_3440_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3438_ == 0 {
                    lean_ctor_set(v___x_3437_, 0, v___x_3440_);
                    v___x_3442_ = v___x_3437_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3443_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3443_, 0, v___x_3440_);
                    v___x_3442_ = v_reuseFailAlloc_3443_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3442_;
            }
            5 => {
                lean_inc_ref(v_arg_3446_);
                v___x_3452_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_arg_3446_, v___y_3451_);
                if lean_obj_tag(v___x_3452_) == 0 {
                    v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
                    v_isSharedCheck_3517_ = (!lean_is_exclusive(v___x_3452_)) as u8;
                    if v_isSharedCheck_3517_ == 0 {
                        v___x_3455_ = v___x_3452_;
                        v_isShared_3456_ = v_isSharedCheck_3517_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3453_);
                        lean_dec(v___x_3452_);
                        v___x_3455_ = lean_box(0);
                        v_isShared_3456_ = v_isSharedCheck_3517_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_arg_3449_);
                    lean_dec_ref(v_arg_3446_);
                    v_a_3518_ = lean_ctor_get(v___x_3452_, 0);
                    v_isSharedCheck_3525_ = (!lean_is_exclusive(v___x_3452_)) as u8;
                    if v_isSharedCheck_3525_ == 0 {
                        v___x_3520_ = v___x_3452_;
                        v_isShared_3521_ = v_isSharedCheck_3525_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_3518_);
                        lean_dec(v___x_3452_);
                        v___x_3520_ = lean_box(0);
                        v_isShared_3521_ = v_isSharedCheck_3525_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3457_ = l_Lean_Expr_cleanupAnnotations(v_a_3453_);
                v___x_3458_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
                v___x_3459_ = l_Lean_Expr_isConstOf(v___x_3457_, v___x_3458_);
                if v___x_3459_ == 0 {
                    v___x_3460_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
                    v___x_3461_ = l_Lean_Expr_isConstOf(v___x_3457_, v___x_3460_);
                    if v___x_3461_ == 0 {
                        lean_dec_ref(v_arg_3446_);
                        v___x_3462_ = l_Lean_Expr_isApp(v___x_3457_);
                        if v___x_3462_ == 0 {
                            lean_dec_ref(v___x_3457_);
                            lean_del_object(v___x_3455_);
                            lean_dec_ref(v_arg_3449_);
                            state = 1;
                            continue;
                        } else {
                            v_arg_3463_ = lean_ctor_get(v___x_3457_, 1);
                            lean_inc_ref(v_arg_3463_);
                            v___x_3464_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3457_);
                            v___x_3465_ = l_Lean_Expr_isApp(v___x_3464_);
                            if v___x_3465_ == 0 {
                                lean_dec_ref(v___x_3464_);
                                lean_dec_ref(v_arg_3463_);
                                lean_del_object(v___x_3455_);
                                lean_dec_ref(v_arg_3449_);
                                state = 1;
                                continue;
                            } else {
                                v_arg_3466_ = lean_ctor_get(v___x_3464_, 1);
                                lean_inc_ref(v_arg_3466_);
                                v___x_3467_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3464_);
                                v___x_3468_ = l_Lean_Meta_Grind_pushNot___redArg___closed__10;
                                v___x_3469_ = l_Lean_Expr_isConstOf(v___x_3467_, v___x_3468_);
                                lean_dec_ref(v___x_3467_);
                                if v___x_3469_ == 0 {
                                    lean_dec_ref(v_arg_3466_);
                                    lean_dec_ref(v_arg_3463_);
                                    lean_del_object(v___x_3455_);
                                    lean_dec_ref(v_arg_3449_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_3470_ = l_Lean_Expr_isForall(v_arg_3449_);
                                    if v___x_3470_ == 0 {
                                        v___x_3471_ = l_Lean_Expr_isForall(v_arg_3466_);
                                        if v___x_3471_ == 0 {
                                            v___x_3472_ = l_Lean_Expr_isForall(v_arg_3463_);
                                            if v___x_3472_ == 0 {
                                                lean_dec_ref(v_arg_3466_);
                                                lean_dec_ref(v_arg_3463_);
                                                lean_dec_ref(v_arg_3449_);
                                                v___x_3473_ =
                                                    l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                                if v_isShared_3456_ == 0 {
                                                    lean_ctor_set(v___x_3455_, 0, v___x_3473_);
                                                    v___x_3475_ = v___x_3455_;
                                                    state = 7;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3476_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_3476_,
                                                        0,
                                                        v___x_3473_,
                                                    );
                                                    v___x_3475_ = v_reuseFailAlloc_3476_;
                                                    state = 7;
                                                    continue;
                                                }
                                            } else {
                                                lean_inc_ref(v_arg_3449_);
                                                lean_inc_ref(v_arg_3466_);
                                                v___x_3477_ = l_Lean_mkOr(v_arg_3466_, v_arg_3449_);
                                                lean_inc_ref(v_arg_3463_);
                                                v___x_3478_ = l_Lean_mkOr(v_arg_3463_, v___x_3477_);
                                                v___x_3479_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__2_once), _init_l_Lean_Meta_Grind_simpOr___redArg___closed__2);
                                                v___x_3480_ = l_Lean_mkApp3(
                                                    v___x_3479_,
                                                    v_arg_3449_,
                                                    v_arg_3466_,
                                                    v_arg_3463_,
                                                );
                                                v___x_3481_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_3481_, 0, v___x_3480_);
                                                v___x_3482_ = lean_alloc_ctor(0, 2, (1) as u32);
                                                lean_ctor_set(v___x_3482_, 0, v___x_3478_);
                                                lean_ctor_set(v___x_3482_, 1, v___x_3481_);
                                                lean_ctor_set_uint8(
                                                    v___x_3482_,
                                                    (core::mem::size_of::<*mut LeanObject>() * 2)
                                                        as u32,
                                                    v___x_3469_,
                                                );
                                                v___x_3483_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_3483_, 0, v___x_3482_);
                                                if v_isShared_3456_ == 0 {
                                                    lean_ctor_set(v___x_3455_, 0, v___x_3483_);
                                                    v___x_3485_ = v___x_3455_;
                                                    state = 8;
                                                    continue;
                                                } else {
                                                    v_reuseFailAlloc_3486_ =
                                                        lean_alloc_ctor(0, 1, (0) as u32);
                                                    lean_ctor_set(
                                                        v_reuseFailAlloc_3486_,
                                                        0,
                                                        v___x_3483_,
                                                    );
                                                    v___x_3485_ = v_reuseFailAlloc_3486_;
                                                    state = 8;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_inc_ref(v_arg_3463_);
                                            lean_inc_ref(v_arg_3449_);
                                            v___x_3487_ = l_Lean_mkOr(v_arg_3449_, v_arg_3463_);
                                            lean_inc_ref(v_arg_3466_);
                                            v___x_3488_ = l_Lean_mkOr(v_arg_3466_, v___x_3487_);
                                            v___x_3489_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__5_once), _init_l_Lean_Meta_Grind_simpOr___redArg___closed__5);
                                            v___x_3490_ = l_Lean_mkApp3(
                                                v___x_3489_,
                                                v_arg_3449_,
                                                v_arg_3466_,
                                                v_arg_3463_,
                                            );
                                            v___x_3491_ = lean_alloc_ctor(1, 1, (0) as u32);
                                            lean_ctor_set(v___x_3491_, 0, v___x_3490_);
                                            v___x_3492_ = lean_alloc_ctor(0, 2, (1) as u32);
                                            lean_ctor_set(v___x_3492_, 0, v___x_3488_);
                                            lean_ctor_set(v___x_3492_, 1, v___x_3491_);
                                            lean_ctor_set_uint8(
                                                v___x_3492_,
                                                (core::mem::size_of::<*mut LeanObject>() * 2)
                                                    as u32,
                                                v___x_3469_,
                                            );
                                            v___x_3493_ = lean_alloc_ctor(1, 1, (0) as u32);
                                            lean_ctor_set(v___x_3493_, 0, v___x_3492_);
                                            if v_isShared_3456_ == 0 {
                                                lean_ctor_set(v___x_3455_, 0, v___x_3493_);
                                                v___x_3495_ = v___x_3455_;
                                                state = 9;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3496_ =
                                                    lean_alloc_ctor(0, 1, (0) as u32);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_3496_,
                                                    0,
                                                    v___x_3493_,
                                                );
                                                v___x_3495_ = v_reuseFailAlloc_3496_;
                                                state = 9;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v_arg_3466_);
                                        lean_dec_ref(v_arg_3463_);
                                        lean_dec_ref(v_arg_3449_);
                                        v___x_3497_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                                        if v_isShared_3456_ == 0 {
                                            lean_ctor_set(v___x_3455_, 0, v___x_3497_);
                                            v___x_3499_ = v___x_3455_;
                                            state = 10;
                                            continue;
                                        } else {
                                            v_reuseFailAlloc_3500_ =
                                                lean_alloc_ctor(0, 1, (0) as u32);
                                            lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
                                            v___x_3499_ = v_reuseFailAlloc_3500_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3457_);
                        v___x_3501_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpOr___redArg___closed__8_once
                            ),
                            _init_l_Lean_Meta_Grind_simpOr___redArg___closed__8,
                        );
                        v___x_3502_ = l_Lean_Expr_app___override(v___x_3501_, v_arg_3449_);
                        v___x_3503_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3503_, 0, v___x_3502_);
                        v___x_3504_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_3504_, 0, v_arg_3446_);
                        lean_ctor_set(v___x_3504_, 1, v___x_3503_);
                        lean_ctor_set_uint8(
                            v___x_3504_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_3461_,
                        );
                        v___x_3505_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3505_, 0, v___x_3504_);
                        if v_isShared_3456_ == 0 {
                            lean_ctor_set(v___x_3455_, 0, v___x_3505_);
                            v___x_3507_ = v___x_3455_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
                            v___x_3507_ = v_reuseFailAlloc_3508_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3457_);
                    lean_dec_ref(v_arg_3446_);
                    v___x_3509_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__11),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpOr___redArg___closed__11_once
                        ),
                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__11,
                    );
                    lean_inc_ref(v_arg_3449_);
                    v___x_3510_ = l_Lean_Expr_app___override(v___x_3509_, v_arg_3449_);
                    v___x_3511_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3511_, 0, v___x_3510_);
                    v___x_3512_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3512_, 0, v_arg_3449_);
                    lean_ctor_set(v___x_3512_, 1, v___x_3511_);
                    lean_ctor_set_uint8(
                        v___x_3512_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_3459_,
                    );
                    v___x_3513_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3513_, 0, v___x_3512_);
                    if v_isShared_3456_ == 0 {
                        lean_ctor_set(v___x_3455_, 0, v___x_3513_);
                        v___x_3515_ = v___x_3455_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3516_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3516_, 0, v___x_3513_);
                        v___x_3515_ = v_reuseFailAlloc_3516_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3475_;
            }
            8 => {
                return v___x_3485_;
            }
            9 => {
                return v___x_3495_;
            }
            10 => {
                return v___x_3499_;
            }
            11 => {
                return v___x_3507_;
            }
            12 => {
                return v___x_3515_;
            }
            13 => {
                if v_isShared_3521_ == 0 {
                    v___x_3523_ = v___x_3520_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
                    v___x_3523_ = v_reuseFailAlloc_3524_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3523_;
            }
            15 => {
                v___x_3534_ = l_Lean_Expr_cleanupAnnotations(v_a_3530_);
                v___x_3535_ = l_Lean_Meta_Grind_simpEq___redArg___closed__8;
                v___x_3536_ = l_Lean_Expr_isConstOf(v___x_3534_, v___x_3535_);
                if v___x_3536_ == 0 {
                    v___x_3537_ = l_Lean_Meta_Grind_simpEq___redArg___closed__5;
                    v___x_3538_ = l_Lean_Expr_isConstOf(v___x_3534_, v___x_3537_);
                    if v___x_3538_ == 0 {
                        v___x_3539_ = l_Lean_Expr_isApp(v___x_3534_);
                        if v___x_3539_ == 0 {
                            lean_dec_ref(v___x_3534_);
                            lean_del_object(v___x_3532_);
                            v___y_3451_ = v_a_3429_;
                            state = 5;
                            continue;
                        } else {
                            v_arg_3540_ = lean_ctor_get(v___x_3534_, 1);
                            lean_inc_ref(v_arg_3540_);
                            v___x_3541_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3534_);
                            v___x_3542_ = l_Lean_Expr_isApp(v___x_3541_);
                            if v___x_3542_ == 0 {
                                lean_dec_ref(v___x_3541_);
                                lean_dec_ref(v_arg_3540_);
                                lean_del_object(v___x_3532_);
                                v___y_3451_ = v_a_3429_;
                                state = 5;
                                continue;
                            } else {
                                v_arg_3543_ = lean_ctor_get(v___x_3541_, 1);
                                lean_inc_ref(v_arg_3543_);
                                v___x_3544_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3541_);
                                v___x_3545_ = l_Lean_Expr_isConstOf(v___x_3544_, v___x_3527_);
                                lean_dec_ref(v___x_3544_);
                                if v___x_3545_ == 0 {
                                    lean_dec_ref(v_arg_3543_);
                                    lean_dec_ref(v_arg_3540_);
                                    lean_del_object(v___x_3532_);
                                    v___y_3451_ = v_a_3429_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec_ref(v_arg_3449_);
                                    lean_inc_ref(v_arg_3446_);
                                    lean_inc_ref(v_arg_3540_);
                                    v___x_3546_ = l_Lean_mkOr(v_arg_3540_, v_arg_3446_);
                                    lean_inc_ref(v_arg_3543_);
                                    v___x_3547_ = l_Lean_mkOr(v_arg_3543_, v___x_3546_);
                                    v___x_3548_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpOr___redArg___closed__14
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Grind_simpOr___redArg___closed__14_once
                                        ),
                                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__14,
                                    );
                                    v___x_3549_ = l_Lean_mkApp3(
                                        v___x_3548_,
                                        v_arg_3543_,
                                        v_arg_3540_,
                                        v_arg_3446_,
                                    );
                                    v___x_3550_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_3550_, 0, v___x_3549_);
                                    v___x_3551_ = lean_alloc_ctor(0, 2, (1) as u32);
                                    lean_ctor_set(v___x_3551_, 0, v___x_3547_);
                                    lean_ctor_set(v___x_3551_, 1, v___x_3550_);
                                    lean_ctor_set_uint8(
                                        v___x_3551_,
                                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                                        v___x_3545_,
                                    );
                                    v___x_3552_ = lean_alloc_ctor(1, 1, (0) as u32);
                                    lean_ctor_set(v___x_3552_, 0, v___x_3551_);
                                    if v_isShared_3533_ == 0 {
                                        lean_ctor_set(v___x_3532_, 0, v___x_3552_);
                                        v___x_3554_ = v___x_3532_;
                                        state = 16;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 1, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_3555_, 0, v___x_3552_);
                                        v___x_3554_ = v_reuseFailAlloc_3555_;
                                        state = 16;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_3534_);
                        v___x_3556_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__17),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_simpOr___redArg___closed__17_once
                            ),
                            _init_l_Lean_Meta_Grind_simpOr___redArg___closed__17,
                        );
                        v___x_3557_ = l_Lean_Expr_app___override(v___x_3556_, v_arg_3446_);
                        v___x_3558_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3558_, 0, v___x_3557_);
                        v___x_3559_ = lean_alloc_ctor(0, 2, (1) as u32);
                        lean_ctor_set(v___x_3559_, 0, v_arg_3449_);
                        lean_ctor_set(v___x_3559_, 1, v___x_3558_);
                        lean_ctor_set_uint8(
                            v___x_3559_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                            v___x_3538_,
                        );
                        v___x_3560_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3560_, 0, v___x_3559_);
                        if v_isShared_3533_ == 0 {
                            lean_ctor_set(v___x_3532_, 0, v___x_3560_);
                            v___x_3562_ = v___x_3532_;
                            state = 17;
                            continue;
                        } else {
                            v_reuseFailAlloc_3563_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3563_, 0, v___x_3560_);
                            v___x_3562_ = v_reuseFailAlloc_3563_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_3534_);
                    lean_dec_ref(v_arg_3449_);
                    v___x_3564_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpOr___redArg___closed__20),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_simpOr___redArg___closed__20_once
                        ),
                        _init_l_Lean_Meta_Grind_simpOr___redArg___closed__20,
                    );
                    lean_inc_ref(v_arg_3446_);
                    v___x_3565_ = l_Lean_Expr_app___override(v___x_3564_, v_arg_3446_);
                    v___x_3566_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3566_, 0, v___x_3565_);
                    v___x_3567_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v___x_3567_, 0, v_arg_3446_);
                    lean_ctor_set(v___x_3567_, 1, v___x_3566_);
                    lean_ctor_set_uint8(
                        v___x_3567_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v___x_3536_,
                    );
                    v___x_3568_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3568_, 0, v___x_3567_);
                    if v_isShared_3533_ == 0 {
                        lean_ctor_set(v___x_3532_, 0, v___x_3568_);
                        v___x_3570_ = v___x_3532_;
                        state = 18;
                        continue;
                    } else {
                        v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3568_);
                        v___x_3570_ = v_reuseFailAlloc_3571_;
                        state = 18;
                        continue;
                    }
                }
            }
            16 => {
                return v___x_3554_;
            }
            17 => {
                return v___x_3562_;
            }
            18 => {
                return v___x_3570_;
            }
            19 => {
                if v_isShared_3576_ == 0 {
                    v___x_3578_ = v___x_3575_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
                    v___x_3578_ = v_reuseFailAlloc_3579_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3578_;
            }
            21 => {
                if v_isShared_3585_ == 0 {
                    v___x_3587_ = v___x_3584_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
                    v___x_3587_ = v_reuseFailAlloc_3588_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3587_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___redArg___boxed(
    mut v_e_3590_: *mut LeanObject,
    mut v_a_3591_: *mut LeanObject,
    mut v_a_3592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3593_: *mut LeanObject = core::ptr::null_mut();
    v_res_3593_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_3590_, v_a_3591_);
    lean_dec(v_a_3591_);
    return v_res_3593_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr(
    mut v_e_3594_: *mut LeanObject,
    mut v_a_3595_: *mut LeanObject,
    mut v_a_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
    mut v_a_3600_: *mut LeanObject,
    mut v_a_3601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_Meta_Grind_simpOr___redArg(v_e_3594_, v_a_3599_);
    return v___x_3603_;
}
pub unsafe fn l_Lean_Meta_Grind_simpOr___boxed(
    mut v_e_3604_: *mut LeanObject,
    mut v_a_3605_: *mut LeanObject,
    mut v_a_3606_: *mut LeanObject,
    mut v_a_3607_: *mut LeanObject,
    mut v_a_3608_: *mut LeanObject,
    mut v_a_3609_: *mut LeanObject,
    mut v_a_3610_: *mut LeanObject,
    mut v_a_3611_: *mut LeanObject,
    mut v_a_3612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3613_: *mut LeanObject = core::ptr::null_mut();
    v_res_3613_ = l_Lean_Meta_Grind_simpOr(
        v_e_3604_, v_a_3605_, v_a_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_, v_a_3611_,
    );
    lean_dec(v_a_3611_);
    lean_dec_ref(v_a_3610_);
    lean_dec(v_a_3609_);
    lean_dec_ref(v_a_3608_);
    lean_dec(v_a_3607_);
    lean_dec_ref(v_a_3606_);
    lean_dec(v_a_3605_);
    return v_res_3613_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_()
-> *mut LeanObject {
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    v___x_3631_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
    v___x_3632_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
    v___x_3633_ = lean_alloc_closure(
        l_Lean_Meta_Grind_simpOr___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_3634_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_3631_, v___x_3632_, v___x_3633_);
    return v___x_3634_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11____boxed(
    mut v_a_3635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3636_: *mut LeanObject = core::ptr::null_mut();
    v_res_3636_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_();
    return v_res_3636_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0() -> u64 {
    let mut v___x_3637_: u8 = 0;
    let mut v___x_3638_: u64 = 0;
    v___x_3637_ = 1;
    v___x_3638_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3637_);
    return v___x_3638_;
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(
    mut v___x_3639_: u8,
    mut v___x_3640_: u8,
    mut v_h_3641_: *mut LeanObject,
    mut v___y_3642_: *mut LeanObject,
    mut v___y_3643_: *mut LeanObject,
    mut v___y_3644_: *mut LeanObject,
    mut v___y_3645_: *mut LeanObject,
    mut v___y_3646_: *mut LeanObject,
    mut v___y_3647_: *mut LeanObject,
    mut v___y_3648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: u8 = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_foApprox_3666_: u8 = 0;
    let mut v_ctxApprox_3667_: u8 = 0;
    let mut v_quasiPatternApprox_3668_: u8 = 0;
    let mut v_constApprox_3669_: u8 = 0;
    let mut v_isDefEqStuckEx_3670_: u8 = 0;
    let mut v_unificationHints_3671_: u8 = 0;
    let mut v_proofIrrelevance_3672_: u8 = 0;
    let mut v_assignSyntheticOpaque_3673_: u8 = 0;
    let mut v_offsetCnstrs_3674_: u8 = 0;
    let mut v_etaStruct_3675_: u8 = 0;
    let mut v_univApprox_3676_: u8 = 0;
    let mut v_iota_3677_: u8 = 0;
    let mut v_beta_3678_: u8 = 0;
    let mut v_proj_3679_: u8 = 0;
    let mut v_zeta_3680_: u8 = 0;
    let mut v_zetaDelta_3681_: u8 = 0;
    let mut v_zetaUnused_3682_: u8 = 0;
    let mut v_zetaHave_3683_: u8 = 0;
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3686_: u8 = 0;
    let mut v_trackZetaDelta_3687_: u8 = 0;
    let mut v_zetaDeltaSet_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_3689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_localInstances_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_3692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_univApprox_3694_: u8 = 0;
    let mut v_inTypeClassResolution_3695_: u8 = 0;
    let mut v_cacheInferType_3696_: u8 = 0;
    let mut v___x_3697_: u8 = 0;
    let mut v_config_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: u64 = 0;
    let mut v___x_3701_: u64 = 0;
    let mut v___x_3702_: u64 = 0;
    let mut v___x_3703_: u64 = 0;
    let mut v___x_3704_: u64 = 0;
    let mut v_key_3705_: u64 = 0;
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3714_: u8 = 0;
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3718_: u8 = 0;
    let mut v_reuseFailAlloc_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3720_: u8 = 0;
    let mut v_a_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3724_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3728_: u8 = 0;
    let mut v_a_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3732_: u8 = 0;
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3736_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3650_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_simpEq___redArg___closed__9_once),
                    _init_l_Lean_Meta_Grind_simpEq___redArg___closed__9,
                );
                lean_inc_ref(v_h_3641_);
                v___x_3657_ = l_Lean_Meta_mkNoConfusion(
                    v___x_3650_,
                    v_h_3641_,
                    v___y_3645_,
                    v___y_3646_,
                    v___y_3647_,
                    v___y_3648_,
                );
                if lean_obj_tag(v___x_3657_) == 0 {
                    v_a_3658_ = lean_ctor_get(v___x_3657_, 0);
                    lean_inc(v_a_3658_);
                    lean_dec_ref_known(v___x_3657_, 1);
                    v___x_3659_ = lean_unsigned_to_nat(1);
                    v___x_3660_ = lean_mk_empty_array_with_capacity(v___x_3659_);
                    v___x_3661_ = lean_array_push(v___x_3660_, v_h_3641_);
                    v___x_3662_ = 1;
                    v___x_3663_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_3661_,
                        v_a_3658_,
                        v___x_3639_,
                        v___x_3640_,
                        v___x_3639_,
                        v___x_3640_,
                        v___x_3662_,
                        v___y_3645_,
                        v___y_3646_,
                        v___y_3647_,
                        v___y_3648_,
                    );
                    lean_dec_ref(v___x_3661_);
                    if lean_obj_tag(v___x_3663_) == 0 {
                        v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
                        lean_inc(v_a_3664_);
                        lean_dec_ref_known(v___x_3663_, 1);
                        v___x_3665_ = l_Lean_Meta_Context_config(v___y_3645_);
                        v_foApprox_3666_ = lean_ctor_get_uint8(v___x_3665_, 0 as u32);
                        v_ctxApprox_3667_ = lean_ctor_get_uint8(v___x_3665_, 1 as u32);
                        v_quasiPatternApprox_3668_ = lean_ctor_get_uint8(v___x_3665_, 2 as u32);
                        v_constApprox_3669_ = lean_ctor_get_uint8(v___x_3665_, 3 as u32);
                        v_isDefEqStuckEx_3670_ = lean_ctor_get_uint8(v___x_3665_, 4 as u32);
                        v_unificationHints_3671_ = lean_ctor_get_uint8(v___x_3665_, 5 as u32);
                        v_proofIrrelevance_3672_ = lean_ctor_get_uint8(v___x_3665_, 6 as u32);
                        v_assignSyntheticOpaque_3673_ = lean_ctor_get_uint8(v___x_3665_, 7 as u32);
                        v_offsetCnstrs_3674_ = lean_ctor_get_uint8(v___x_3665_, 8 as u32);
                        v_etaStruct_3675_ = lean_ctor_get_uint8(v___x_3665_, 10 as u32);
                        v_univApprox_3676_ = lean_ctor_get_uint8(v___x_3665_, 11 as u32);
                        v_iota_3677_ = lean_ctor_get_uint8(v___x_3665_, 12 as u32);
                        v_beta_3678_ = lean_ctor_get_uint8(v___x_3665_, 13 as u32);
                        v_proj_3679_ = lean_ctor_get_uint8(v___x_3665_, 14 as u32);
                        v_zeta_3680_ = lean_ctor_get_uint8(v___x_3665_, 15 as u32);
                        v_zetaDelta_3681_ = lean_ctor_get_uint8(v___x_3665_, 16 as u32);
                        v_zetaUnused_3682_ = lean_ctor_get_uint8(v___x_3665_, 17 as u32);
                        v_zetaHave_3683_ = lean_ctor_get_uint8(v___x_3665_, 18 as u32);
                        v_isSharedCheck_3720_ = (!lean_is_exclusive(v___x_3665_)) as u8;
                        if v_isSharedCheck_3720_ == 0 {
                            v___x_3685_ = v___x_3665_;
                            v_isShared_3686_ = v_isSharedCheck_3720_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3665_);
                            v___x_3685_ = lean_box(0);
                            v_isShared_3686_ = v_isSharedCheck_3720_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_3721_ = lean_ctor_get(v___x_3663_, 0);
                        v_isSharedCheck_3728_ = (!lean_is_exclusive(v___x_3663_)) as u8;
                        if v_isSharedCheck_3728_ == 0 {
                            v___x_3723_ = v___x_3663_;
                            v_isShared_3724_ = v_isSharedCheck_3728_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3721_);
                            lean_dec(v___x_3663_);
                            v___x_3723_ = lean_box(0);
                            v_isShared_3724_ = v_isSharedCheck_3728_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_h_3641_);
                    v_a_3729_ = lean_ctor_get(v___x_3657_, 0);
                    v_isSharedCheck_3736_ = (!lean_is_exclusive(v___x_3657_)) as u8;
                    if v_isSharedCheck_3736_ == 0 {
                        v___x_3731_ = v___x_3657_;
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3729_);
                        lean_dec(v___x_3657_);
                        v___x_3731_ = lean_box(0);
                        v_isShared_3732_ = v_isSharedCheck_3736_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3653_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3653_, 0, v_a_3652_);
                v___x_3654_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3654_, 0, v___x_3650_);
                lean_ctor_set(v___x_3654_, 1, v___x_3653_);
                lean_ctor_set_uint8(
                    v___x_3654_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_3640_,
                );
                v___x_3655_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3655_, 0, v___x_3654_);
                v___x_3656_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3656_, 0, v___x_3655_);
                return v___x_3656_;
            }
            2 => {
                v_trackZetaDelta_3687_ = lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_3688_ = lean_ctor_get(v___y_3645_, 1);
                v_lctx_3689_ = lean_ctor_get(v___y_3645_, 2);
                v_localInstances_3690_ = lean_ctor_get(v___y_3645_, 3);
                v_defEqCtx_x3f_3691_ = lean_ctor_get(v___y_3645_, 4);
                v_synthPendingDepth_3692_ = lean_ctor_get(v___y_3645_, 5);
                v_canUnfold_x3f_3693_ = lean_ctor_get(v___y_3645_, 6);
                v_univApprox_3694_ = lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_3695_ = lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_3696_ = lean_ctor_get_uint8(
                    v___y_3645_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                );
                v___x_3697_ = 1;
                if v_isShared_3686_ == 0 {
                    v_config_3699_ = v___x_3685_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3719_ = lean_alloc_ctor(0, 0, (19) as u32);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 0 as u32, v_foApprox_3666_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 1 as u32, v_ctxApprox_3667_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        2 as u32,
                        v_quasiPatternApprox_3668_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 3 as u32, v_constApprox_3669_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 4 as u32, v_isDefEqStuckEx_3670_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 5 as u32, v_unificationHints_3671_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 6 as u32, v_proofIrrelevance_3672_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_3719_,
                        7 as u32,
                        v_assignSyntheticOpaque_3673_,
                    );
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 8 as u32, v_offsetCnstrs_3674_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 10 as u32, v_etaStruct_3675_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 11 as u32, v_univApprox_3676_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 12 as u32, v_iota_3677_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 13 as u32, v_beta_3678_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 14 as u32, v_proj_3679_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 15 as u32, v_zeta_3680_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 16 as u32, v_zetaDelta_3681_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 17 as u32, v_zetaUnused_3682_);
                    lean_ctor_set_uint8(v_reuseFailAlloc_3719_, 18 as u32, v_zetaHave_3683_);
                    v_config_3699_ = v_reuseFailAlloc_3719_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(v_config_3699_, 9 as u32, v___x_3697_);
                v___x_3700_ = l_Lean_Meta_Context_configKey(v___y_3645_);
                v___x_3701_ = 3u64;
                v___x_3702_ = lean_uint64_shift_right(v___x_3700_, v___x_3701_);
                v___x_3703_ = lean_uint64_shift_left(v___x_3702_, v___x_3701_);
                v___x_3704_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0_once
                    ),
                    _init_l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___closed__0,
                );
                v_key_3705_ = lean_uint64_lor(v___x_3703_, v___x_3704_);
                v___x_3706_ = lean_alloc_ctor(0, 1, (8) as u32);
                lean_ctor_set(v___x_3706_, 0, v_config_3699_);
                lean_ctor_set_uint64(
                    v___x_3706_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_key_3705_,
                );
                lean_inc(v_canUnfold_x3f_3693_);
                lean_inc(v_synthPendingDepth_3692_);
                lean_inc(v_defEqCtx_x3f_3691_);
                lean_inc_ref(v_localInstances_3690_);
                lean_inc_ref(v_lctx_3689_);
                lean_inc(v_zetaDeltaSet_3688_);
                v___x_3707_ = lean_alloc_ctor(0, 7, (4) as u32);
                lean_ctor_set(v___x_3707_, 0, v___x_3706_);
                lean_ctor_set(v___x_3707_, 1, v_zetaDeltaSet_3688_);
                lean_ctor_set(v___x_3707_, 2, v_lctx_3689_);
                lean_ctor_set(v___x_3707_, 3, v_localInstances_3690_);
                lean_ctor_set(v___x_3707_, 4, v_defEqCtx_x3f_3691_);
                lean_ctor_set(v___x_3707_, 5, v_synthPendingDepth_3692_);
                lean_ctor_set(v___x_3707_, 6, v_canUnfold_x3f_3693_);
                lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                    v_trackZetaDelta_3687_,
                );
                lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 1) as u32,
                    v_univApprox_3694_,
                );
                lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_3695_,
                );
                lean_ctor_set_uint8(
                    v___x_3707_,
                    (core::mem::size_of::<*mut LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_3696_,
                );
                v___x_3708_ = l_Lean_Meta_mkEqFalse_x27(
                    v_a_3664_,
                    v___x_3707_,
                    v___y_3646_,
                    v___y_3647_,
                    v___y_3648_,
                );
                lean_dec_ref_known(v___x_3707_, 7);
                if lean_obj_tag(v___x_3708_) == 0 {
                    v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
                    lean_inc(v_a_3709_);
                    lean_dec_ref_known(v___x_3708_, 1);
                    v_a_3652_ = v_a_3709_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v___x_3708_) == 0 {
                        v_a_3710_ = lean_ctor_get(v___x_3708_, 0);
                        lean_inc(v_a_3710_);
                        lean_dec_ref_known(v___x_3708_, 1);
                        v_a_3652_ = v_a_3710_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3711_ = lean_ctor_get(v___x_3708_, 0);
                        v_isSharedCheck_3718_ = (!lean_is_exclusive(v___x_3708_)) as u8;
                        if v_isSharedCheck_3718_ == 0 {
                            v___x_3713_ = v___x_3708_;
                            v_isShared_3714_ = v_isSharedCheck_3718_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3711_);
                            lean_dec(v___x_3708_);
                            v___x_3713_ = lean_box(0);
                            v_isShared_3714_ = v_isSharedCheck_3718_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            4 => {
                if v_isShared_3714_ == 0 {
                    v___x_3716_ = v___x_3713_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
                    v___x_3716_ = v_reuseFailAlloc_3717_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3716_;
            }
            6 => {
                if v_isShared_3724_ == 0 {
                    v___x_3726_ = v___x_3723_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
                    v___x_3726_ = v_reuseFailAlloc_3727_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3726_;
            }
            8 => {
                if v_isShared_3732_ == 0 {
                    v___x_3734_ = v___x_3731_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
                    v___x_3734_ = v_reuseFailAlloc_3735_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3734_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed(
    mut v___x_3737_: *mut LeanObject,
    mut v___x_3738_: *mut LeanObject,
    mut v_h_3739_: *mut LeanObject,
    mut v___y_3740_: *mut LeanObject,
    mut v___y_3741_: *mut LeanObject,
    mut v___y_3742_: *mut LeanObject,
    mut v___y_3743_: *mut LeanObject,
    mut v___y_3744_: *mut LeanObject,
    mut v___y_3745_: *mut LeanObject,
    mut v___y_3746_: *mut LeanObject,
    mut v___y_3747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_18057__boxed_3748_: u8 = 0;
    let mut v___x_18058__boxed_3749_: u8 = 0;
    let mut v_res_3750_: *mut LeanObject = core::ptr::null_mut();
    v___x_18057__boxed_3748_ = (lean_unbox(v___x_3737_) as u8);
    v___x_18058__boxed_3749_ = (lean_unbox(v___x_3738_) as u8);
    v_res_3750_ = l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0(
        v___x_18057__boxed_3748_,
        v___x_18058__boxed_3749_,
        v_h_3739_,
        v___y_3740_,
        v___y_3741_,
        v___y_3742_,
        v___y_3743_,
        v___y_3744_,
        v___y_3745_,
        v___y_3746_,
    );
    lean_dec(v___y_3746_);
    lean_dec_ref(v___y_3745_);
    lean_dec(v___y_3744_);
    lean_dec_ref(v___y_3743_);
    lean_dec(v___y_3742_);
    lean_dec_ref(v___y_3741_);
    lean_dec(v___y_3740_);
    return v_res_3750_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(
    mut v_k_3751_: *mut LeanObject,
    mut v___y_3752_: *mut LeanObject,
    mut v___y_3753_: *mut LeanObject,
    mut v___y_3754_: *mut LeanObject,
    mut v_b_3755_: *mut LeanObject,
    mut v___y_3756_: *mut LeanObject,
    mut v___y_3757_: *mut LeanObject,
    mut v___y_3758_: *mut LeanObject,
    mut v___y_3759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3759_);
    lean_inc_ref(v___y_3758_);
    lean_inc(v___y_3757_);
    lean_inc_ref(v___y_3756_);
    lean_inc(v___y_3754_);
    lean_inc_ref(v___y_3753_);
    lean_inc(v___y_3752_);
    v___x_3761_ = lean_apply_9(
        v_k_3751_,
        v_b_3755_,
        v___y_3752_,
        v___y_3753_,
        v___y_3754_,
        v___y_3756_,
        v___y_3757_,
        v___y_3758_,
        v___y_3759_,
        lean_box(0),
    );
    return v___x_3761_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_3762_: *mut LeanObject,
    mut v___y_3763_: *mut LeanObject,
    mut v___y_3764_: *mut LeanObject,
    mut v___y_3765_: *mut LeanObject,
    mut v_b_3766_: *mut LeanObject,
    mut v___y_3767_: *mut LeanObject,
    mut v___y_3768_: *mut LeanObject,
    mut v___y_3769_: *mut LeanObject,
    mut v___y_3770_: *mut LeanObject,
    mut v___y_3771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3772_: *mut LeanObject = core::ptr::null_mut();
    v_res_3772_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0(v_k_3762_, v___y_3763_, v___y_3764_, v___y_3765_, v_b_3766_, v___y_3767_, v___y_3768_, v___y_3769_, v___y_3770_);
    lean_dec(v___y_3770_);
    lean_dec_ref(v___y_3769_);
    lean_dec(v___y_3768_);
    lean_dec_ref(v___y_3767_);
    lean_dec(v___y_3765_);
    lean_dec_ref(v___y_3764_);
    lean_dec(v___y_3763_);
    return v_res_3772_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(
    mut v_name_3773_: *mut LeanObject,
    mut v_bi_3774_: u8,
    mut v_type_3775_: *mut LeanObject,
    mut v_k_3776_: *mut LeanObject,
    mut v_kind_3777_: u8,
    mut v___y_3778_: *mut LeanObject,
    mut v___y_3779_: *mut LeanObject,
    mut v___y_3780_: *mut LeanObject,
    mut v___y_3781_: *mut LeanObject,
    mut v___y_3782_: *mut LeanObject,
    mut v___y_3783_: *mut LeanObject,
    mut v___y_3784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3791_: u8 = 0;
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3795_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3780_);
                lean_inc_ref(v___y_3779_);
                lean_inc(v___y_3778_);
                v___f_3786_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 4);
                lean_closure_set(v___f_3786_, 0, v_k_3776_);
                lean_closure_set(v___f_3786_, 1, v___y_3778_);
                lean_closure_set(v___f_3786_, 2, v___y_3779_);
                lean_closure_set(v___f_3786_, 3, v___y_3780_);
                v___x_3787_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_3773_,
                    v_bi_3774_,
                    v_type_3775_,
                    v___f_3786_,
                    v_kind_3777_,
                    v___y_3781_,
                    v___y_3782_,
                    v___y_3783_,
                    v___y_3784_,
                );
                if lean_obj_tag(v___x_3787_) == 0 {
                    return v___x_3787_;
                } else {
                    v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
                    v_isSharedCheck_3795_ = (!lean_is_exclusive(v___x_3787_)) as u8;
                    if v_isSharedCheck_3795_ == 0 {
                        v___x_3790_ = v___x_3787_;
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3788_);
                        lean_dec(v___x_3787_);
                        v___x_3790_ = lean_box(0);
                        v_isShared_3791_ = v_isSharedCheck_3795_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3791_ == 0 {
                    v___x_3793_ = v___x_3790_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
                    v___x_3793_ = v_reuseFailAlloc_3794_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3793_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg___boxed(
    mut v_name_3796_: *mut LeanObject,
    mut v_bi_3797_: *mut LeanObject,
    mut v_type_3798_: *mut LeanObject,
    mut v_k_3799_: *mut LeanObject,
    mut v_kind_3800_: *mut LeanObject,
    mut v___y_3801_: *mut LeanObject,
    mut v___y_3802_: *mut LeanObject,
    mut v___y_3803_: *mut LeanObject,
    mut v___y_3804_: *mut LeanObject,
    mut v___y_3805_: *mut LeanObject,
    mut v___y_3806_: *mut LeanObject,
    mut v___y_3807_: *mut LeanObject,
    mut v___y_3808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3809_: u8 = 0;
    let mut v_kind_boxed_3810_: u8 = 0;
    let mut v_res_3811_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3809_ = (lean_unbox(v_bi_3797_) as u8);
    v_kind_boxed_3810_ = (lean_unbox(v_kind_3800_) as u8);
    v_res_3811_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3796_, v_bi_boxed_3809_, v_type_3798_, v_k_3799_, v_kind_boxed_3810_, v___y_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_, v___y_3806_, v___y_3807_);
    lean_dec(v___y_3807_);
    lean_dec_ref(v___y_3806_);
    lean_dec(v___y_3805_);
    lean_dec_ref(v___y_3804_);
    lean_dec(v___y_3803_);
    lean_dec_ref(v___y_3802_);
    lean_dec(v___y_3801_);
    return v_res_3811_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(
    mut v_name_3812_: *mut LeanObject,
    mut v_type_3813_: *mut LeanObject,
    mut v_k_3814_: *mut LeanObject,
    mut v___y_3815_: *mut LeanObject,
    mut v___y_3816_: *mut LeanObject,
    mut v___y_3817_: *mut LeanObject,
    mut v___y_3818_: *mut LeanObject,
    mut v___y_3819_: *mut LeanObject,
    mut v___y_3820_: *mut LeanObject,
    mut v___y_3821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3823_: u8 = 0;
    let mut v___x_3824_: u8 = 0;
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    v___x_3823_ = 0;
    v___x_3824_ = 0;
    v___x_3825_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3812_, v___x_3823_, v_type_3813_, v_k_3814_, v___x_3824_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
    return v___x_3825_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg___boxed(
    mut v_name_3826_: *mut LeanObject,
    mut v_type_3827_: *mut LeanObject,
    mut v_k_3828_: *mut LeanObject,
    mut v___y_3829_: *mut LeanObject,
    mut v___y_3830_: *mut LeanObject,
    mut v___y_3831_: *mut LeanObject,
    mut v___y_3832_: *mut LeanObject,
    mut v___y_3833_: *mut LeanObject,
    mut v___y_3834_: *mut LeanObject,
    mut v___y_3835_: *mut LeanObject,
    mut v___y_3836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3837_: *mut LeanObject = core::ptr::null_mut();
    v_res_3837_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(
            v_name_3826_,
            v_type_3827_,
            v_k_3828_,
            v___y_3829_,
            v___y_3830_,
            v___y_3831_,
            v___y_3832_,
            v___y_3833_,
            v___y_3834_,
            v___y_3835_,
        );
    lean_dec(v___y_3835_);
    lean_dec_ref(v___y_3834_);
    lean_dec(v___y_3833_);
    lean_dec_ref(v___y_3832_);
    lean_dec(v___y_3831_);
    lean_dec_ref(v___y_3830_);
    lean_dec(v___y_3829_);
    return v_res_3837_;
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap(
    mut v_e_3841_: *mut LeanObject,
    mut v_a_3842_: *mut LeanObject,
    mut v_a_3843_: *mut LeanObject,
    mut v_a_3844_: *mut LeanObject,
    mut v_a_3845_: *mut LeanObject,
    mut v_a_3846_: *mut LeanObject,
    mut v_a_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3854_: u8 = 0;
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3861_: u8 = 0;
    let mut v_arg_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: u8 = 0;
    let mut v_arg_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: u8 = 0;
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3875_: u8 = 0;
    let mut v_val_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3881_: u8 = 0;
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: u8 = 0;
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3902_: u8 = 0;
    let mut v_a_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3906_: u8 = 0;
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3915_: u8 = 0;
    let mut v_a_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3919_: u8 = 0;
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3923_: u8 = 0;
    let mut v_isSharedCheck_3924_: u8 = 0;
    let mut v_a_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3928_: u8 = 0;
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_3841_);
                v___x_3850_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3841_, v_a_3846_);
                if lean_obj_tag(v___x_3850_) == 0 {
                    v_a_3851_ = lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3924_ = (!lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3924_ == 0 {
                        v___x_3853_ = v___x_3850_;
                        v_isShared_3854_ = v_isSharedCheck_3924_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3851_);
                        lean_dec(v___x_3850_);
                        v___x_3853_ = lean_box(0);
                        v_isShared_3854_ = v_isSharedCheck_3924_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3841_);
                    v_a_3925_ = lean_ctor_get(v___x_3850_, 0);
                    v_isSharedCheck_3932_ = (!lean_is_exclusive(v___x_3850_)) as u8;
                    if v_isSharedCheck_3932_ == 0 {
                        v___x_3927_ = v___x_3850_;
                        v_isShared_3928_ = v_isSharedCheck_3932_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_3925_);
                        lean_dec(v___x_3850_);
                        v___x_3927_ = lean_box(0);
                        v_isShared_3928_ = v_isSharedCheck_3932_;
                        state = 14;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3860_ = l_Lean_Expr_cleanupAnnotations(v_a_3851_);
                v___x_3861_ = l_Lean_Expr_isApp(v___x_3860_);
                if v___x_3861_ == 0 {
                    lean_dec_ref(v___x_3860_);
                    lean_dec_ref(v_e_3841_);
                    state = 2;
                    continue;
                } else {
                    v_arg_3862_ = lean_ctor_get(v___x_3860_, 1);
                    lean_inc_ref(v_arg_3862_);
                    v___x_3863_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3860_);
                    v___x_3864_ = l_Lean_Expr_isApp(v___x_3863_);
                    if v___x_3864_ == 0 {
                        lean_dec_ref(v___x_3863_);
                        lean_dec_ref(v_arg_3862_);
                        lean_dec_ref(v_e_3841_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_3865_ = lean_ctor_get(v___x_3863_, 1);
                        lean_inc_ref(v_arg_3865_);
                        v___x_3866_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3863_);
                        v___x_3867_ = l_Lean_Expr_isApp(v___x_3866_);
                        if v___x_3867_ == 0 {
                            lean_dec_ref(v___x_3866_);
                            lean_dec_ref(v_arg_3865_);
                            lean_dec_ref(v_arg_3862_);
                            lean_dec_ref(v_e_3841_);
                            state = 2;
                            continue;
                        } else {
                            v___x_3868_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3866_);
                            v___x_3869_ = l_Lean_Meta_Grind_simpEq___redArg___closed__2;
                            v___x_3870_ = l_Lean_Expr_isConstOf(v___x_3868_, v___x_3869_);
                            lean_dec_ref(v___x_3868_);
                            if v___x_3870_ == 0 {
                                lean_dec_ref(v_arg_3865_);
                                lean_dec_ref(v_arg_3862_);
                                lean_dec_ref(v_e_3841_);
                                state = 2;
                                continue;
                            } else {
                                lean_del_object(v___x_3853_);
                                v___x_3871_ = l_Lean_Meta_isConstructorApp_x3f(
                                    v_arg_3865_,
                                    v_a_3845_,
                                    v_a_3846_,
                                    v_a_3847_,
                                    v_a_3848_,
                                );
                                if lean_obj_tag(v___x_3871_) == 0 {
                                    v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
                                    v_isSharedCheck_3915_ = (!lean_is_exclusive(v___x_3871_)) as u8;
                                    if v_isSharedCheck_3915_ == 0 {
                                        v___x_3874_ = v___x_3871_;
                                        v_isShared_3875_ = v_isSharedCheck_3915_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3872_);
                                        lean_dec(v___x_3871_);
                                        v___x_3874_ = lean_box(0);
                                        v_isShared_3875_ = v_isSharedCheck_3915_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_arg_3862_);
                                    lean_dec_ref(v_e_3841_);
                                    v_a_3916_ = lean_ctor_get(v___x_3871_, 0);
                                    v_isSharedCheck_3923_ = (!lean_is_exclusive(v___x_3871_)) as u8;
                                    if v_isSharedCheck_3923_ == 0 {
                                        v___x_3918_ = v___x_3871_;
                                        v_isShared_3919_ = v_isSharedCheck_3923_;
                                        state = 12;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3916_);
                                        lean_dec(v___x_3871_);
                                        v___x_3918_ = lean_box(0);
                                        v_isShared_3919_ = v_isSharedCheck_3923_;
                                        state = 12;
                                        continue;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_3856_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3854_ == 0 {
                    lean_ctor_set(v___x_3853_, 0, v___x_3856_);
                    v___x_3858_ = v___x_3853_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3859_, 0, v___x_3856_);
                    v___x_3858_ = v_reuseFailAlloc_3859_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3858_;
            }
            4 => {
                if lean_obj_tag(v_a_3872_) == 1 {
                    v_val_3876_ = lean_ctor_get(v_a_3872_, 0);
                    lean_inc(v_val_3876_);
                    lean_dec_ref_known(v_a_3872_, 1);
                    v___x_3877_ = l_Lean_Meta_isConstructorApp_x3f(
                        v_arg_3862_,
                        v_a_3845_,
                        v_a_3846_,
                        v_a_3847_,
                        v_a_3848_,
                    );
                    if lean_obj_tag(v___x_3877_) == 0 {
                        v_a_3878_ = lean_ctor_get(v___x_3877_, 0);
                        v_isSharedCheck_3902_ = (!lean_is_exclusive(v___x_3877_)) as u8;
                        if v_isSharedCheck_3902_ == 0 {
                            v___x_3880_ = v___x_3877_;
                            v_isShared_3881_ = v_isSharedCheck_3902_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3878_);
                            lean_dec(v___x_3877_);
                            v___x_3880_ = lean_box(0);
                            v_isShared_3881_ = v_isSharedCheck_3902_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3876_);
                        lean_del_object(v___x_3874_);
                        lean_dec_ref(v_e_3841_);
                        v_a_3903_ = lean_ctor_get(v___x_3877_, 0);
                        v_isSharedCheck_3910_ = (!lean_is_exclusive(v___x_3877_)) as u8;
                        if v_isSharedCheck_3910_ == 0 {
                            v___x_3905_ = v___x_3877_;
                            v_isShared_3906_ = v_isSharedCheck_3910_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3903_);
                            lean_dec(v___x_3877_);
                            v___x_3905_ = lean_box(0);
                            v_isShared_3906_ = v_isSharedCheck_3910_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_3872_);
                    lean_dec_ref(v_arg_3862_);
                    lean_dec_ref(v_e_3841_);
                    v___x_3911_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_3875_ == 0 {
                        lean_ctor_set(v___x_3874_, 0, v___x_3911_);
                        v___x_3913_ = v___x_3874_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3914_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3911_);
                        v___x_3913_ = v_reuseFailAlloc_3914_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_3878_) == 1 {
                    lean_del_object(v___x_3874_);
                    v_toConstantVal_3887_ = lean_ctor_get(v_val_3876_, 0);
                    lean_inc_ref(v_toConstantVal_3887_);
                    lean_dec(v_val_3876_);
                    v_val_3888_ = lean_ctor_get(v_a_3878_, 0);
                    lean_inc(v_val_3888_);
                    lean_dec_ref_known(v_a_3878_, 1);
                    v_toConstantVal_3889_ = lean_ctor_get(v_val_3888_, 0);
                    lean_inc_ref(v_toConstantVal_3889_);
                    lean_dec(v_val_3888_);
                    v_name_3890_ = lean_ctor_get(v_toConstantVal_3887_, 0);
                    lean_inc(v_name_3890_);
                    lean_dec_ref(v_toConstantVal_3887_);
                    v_name_3891_ = lean_ctor_get(v_toConstantVal_3889_, 0);
                    lean_inc(v_name_3891_);
                    lean_dec_ref(v_toConstantVal_3889_);
                    v___x_3892_ = lean_name_eq(v_name_3890_, v_name_3891_);
                    lean_dec(v_name_3891_);
                    lean_dec(v_name_3890_);
                    if v___x_3892_ == 0 {
                        if v___x_3870_ == 0 {
                            lean_dec_ref(v_e_3841_);
                            state = 6;
                            continue;
                        } else {
                            lean_del_object(v___x_3880_);
                            v___x_3893_ = lean_box((v___x_3892_) as usize);
                            v___x_3894_ = lean_box((v___x_3870_) as usize);
                            v___f_3895_ = lean_alloc_closure(
                                l_Lean_Meta_Grind_reduceCtorEqCheap___lam__0___boxed
                                    as *mut core::ffi::c_void,
                                11,
                                2,
                            );
                            lean_closure_set(v___f_3895_, 0, v___x_3893_);
                            lean_closure_set(v___f_3895_, 1, v___x_3894_);
                            v___x_3896_ = l_Lean_Meta_Grind_reduceCtorEqCheap___closed__1;
                            v___x_3897_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(v___x_3896_, v_e_3841_, v___f_3895_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
                            return v___x_3897_;
                        }
                    } else {
                        lean_dec_ref(v_e_3841_);
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3880_);
                    lean_dec(v_a_3878_);
                    lean_dec(v_val_3876_);
                    lean_dec_ref(v_e_3841_);
                    v___x_3898_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                    if v_isShared_3875_ == 0 {
                        lean_ctor_set(v___x_3874_, 0, v___x_3898_);
                        v___x_3900_ = v___x_3874_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3901_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3898_);
                        v___x_3900_ = v_reuseFailAlloc_3901_;
                        state = 8;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3883_ = l_Lean_Meta_Grind_simpEq___redArg___closed__0;
                if v_isShared_3881_ == 0 {
                    lean_ctor_set(v___x_3880_, 0, v___x_3883_);
                    v___x_3885_ = v___x_3880_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3886_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3883_);
                    v___x_3885_ = v_reuseFailAlloc_3886_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3885_;
            }
            8 => {
                return v___x_3900_;
            }
            9 => {
                if v_isShared_3906_ == 0 {
                    v___x_3908_ = v___x_3905_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_a_3903_);
                    v___x_3908_ = v_reuseFailAlloc_3909_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3908_;
            }
            11 => {
                return v___x_3913_;
            }
            12 => {
                if v_isShared_3919_ == 0 {
                    v___x_3921_ = v___x_3918_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
                    v___x_3921_ = v_reuseFailAlloc_3922_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3921_;
            }
            14 => {
                if v_isShared_3928_ == 0 {
                    v___x_3930_ = v___x_3927_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
                    v___x_3930_ = v_reuseFailAlloc_3931_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_reduceCtorEqCheap___boxed(
    mut v_e_3933_: *mut LeanObject,
    mut v_a_3934_: *mut LeanObject,
    mut v_a_3935_: *mut LeanObject,
    mut v_a_3936_: *mut LeanObject,
    mut v_a_3937_: *mut LeanObject,
    mut v_a_3938_: *mut LeanObject,
    mut v_a_3939_: *mut LeanObject,
    mut v_a_3940_: *mut LeanObject,
    mut v_a_3941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3942_: *mut LeanObject = core::ptr::null_mut();
    v_res_3942_ = l_Lean_Meta_Grind_reduceCtorEqCheap(
        v_e_3933_, v_a_3934_, v_a_3935_, v_a_3936_, v_a_3937_, v_a_3938_, v_a_3939_, v_a_3940_,
    );
    lean_dec(v_a_3940_);
    lean_dec_ref(v_a_3939_);
    lean_dec(v_a_3938_);
    lean_dec_ref(v_a_3937_);
    lean_dec(v_a_3936_);
    lean_dec_ref(v_a_3935_);
    lean_dec(v_a_3934_);
    return v_res_3942_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(
    mut v_00_u03b1_3943_: *mut LeanObject,
    mut v_name_3944_: *mut LeanObject,
    mut v_bi_3945_: u8,
    mut v_type_3946_: *mut LeanObject,
    mut v_k_3947_: *mut LeanObject,
    mut v_kind_3948_: u8,
    mut v___y_3949_: *mut LeanObject,
    mut v___y_3950_: *mut LeanObject,
    mut v___y_3951_: *mut LeanObject,
    mut v___y_3952_: *mut LeanObject,
    mut v___y_3953_: *mut LeanObject,
    mut v___y_3954_: *mut LeanObject,
    mut v___y_3955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    v___x_3957_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___redArg(v_name_3944_, v_bi_3945_, v_type_3946_, v_k_3947_, v_kind_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
    return v___x_3957_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0___boxed(
    mut v_00_u03b1_3958_: *mut LeanObject,
    mut v_name_3959_: *mut LeanObject,
    mut v_bi_3960_: *mut LeanObject,
    mut v_type_3961_: *mut LeanObject,
    mut v_k_3962_: *mut LeanObject,
    mut v_kind_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
    mut v___y_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
    mut v___y_3971_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3972_: u8 = 0;
    let mut v_kind_boxed_3973_: u8 = 0;
    let mut v_res_3974_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3972_ = (lean_unbox(v_bi_3960_) as u8);
    v_kind_boxed_3973_ = (lean_unbox(v_kind_3963_) as u8);
    v_res_3974_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0_spec__0(v_00_u03b1_3958_, v_name_3959_, v_bi_boxed_3972_, v_type_3961_, v_k_3962_, v_kind_boxed_3973_, v___y_3964_, v___y_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_, v___y_3970_);
    lean_dec(v___y_3970_);
    lean_dec_ref(v___y_3969_);
    lean_dec(v___y_3968_);
    lean_dec_ref(v___y_3967_);
    lean_dec(v___y_3966_);
    lean_dec_ref(v___y_3965_);
    lean_dec(v___y_3964_);
    return v_res_3974_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(
    mut v_00_u03b1_3975_: *mut LeanObject,
    mut v_name_3976_: *mut LeanObject,
    mut v_type_3977_: *mut LeanObject,
    mut v_k_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    v___x_3987_ =
        l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___redArg(
            v_name_3976_,
            v_type_3977_,
            v_k_3978_,
            v___y_3979_,
            v___y_3980_,
            v___y_3981_,
            v___y_3982_,
            v___y_3983_,
            v___y_3984_,
            v___y_3985_,
        );
    return v___x_3987_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0___boxed(
    mut v_00_u03b1_3988_: *mut LeanObject,
    mut v_name_3989_: *mut LeanObject,
    mut v_type_3990_: *mut LeanObject,
    mut v_k_3991_: *mut LeanObject,
    mut v___y_3992_: *mut LeanObject,
    mut v___y_3993_: *mut LeanObject,
    mut v___y_3994_: *mut LeanObject,
    mut v___y_3995_: *mut LeanObject,
    mut v___y_3996_: *mut LeanObject,
    mut v___y_3997_: *mut LeanObject,
    mut v___y_3998_: *mut LeanObject,
    mut v___y_3999_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4000_: *mut LeanObject = core::ptr::null_mut();
    v_res_4000_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_Grind_reduceCtorEqCheap_spec__0(
        v_00_u03b1_3988_,
        v_name_3989_,
        v_type_3990_,
        v_k_3991_,
        v___y_3992_,
        v___y_3993_,
        v___y_3994_,
        v___y_3995_,
        v___y_3996_,
        v___y_3997_,
        v___y_3998_,
    );
    lean_dec(v___y_3998_);
    lean_dec_ref(v___y_3997_);
    lean_dec(v___y_3996_);
    lean_dec_ref(v___y_3995_);
    lean_dec(v___y_3994_);
    lean_dec_ref(v___y_3993_);
    lean_dec(v___y_3992_);
    return v_res_4000_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_()
-> *mut LeanObject {
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4011_: *mut LeanObject = core::ptr::null_mut();
    v___x_4008_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_;
    v___x_4009_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__4_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
    v___x_4010_ = lean_alloc_closure(
        l_Lean_Meta_Grind_reduceCtorEqCheap___boxed as *mut core::ffi::c_void,
        9,
        0,
    );
    v___x_4011_ = l_Lean_Meta_Simp_registerBuiltinSimproc(v___x_4008_, v___x_4009_, v___x_4010_);
    return v___x_4011_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13____boxed(
    mut v_a_4012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4013_: *mut LeanObject = core::ptr::null_mut();
    v_res_4013_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_();
    return v_res_4013_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(
    mut v_e_4014_: *mut LeanObject,
    mut v_a_4015_: *mut LeanObject,
    mut v_a_4016_: *mut LeanObject,
    mut v_a_4017_: *mut LeanObject,
    mut v_a_4018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4020_: *mut LeanObject = core::ptr::null_mut();
    v___x_4020_ =
        l_Lean_Meta_Sym_unfoldReducibleStep(v_e_4014_, v_a_4015_, v_a_4016_, v_a_4017_, v_a_4018_);
    return v___x_4020_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg___boxed(
    mut v_e_4021_: *mut LeanObject,
    mut v_a_4022_: *mut LeanObject,
    mut v_a_4023_: *mut LeanObject,
    mut v_a_4024_: *mut LeanObject,
    mut v_a_4025_: *mut LeanObject,
    mut v_a_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4027_: *mut LeanObject = core::ptr::null_mut();
    v_res_4027_ = l_Lean_Meta_Grind_unfoldReducibleSimproc___redArg(
        v_e_4021_, v_a_4022_, v_a_4023_, v_a_4024_, v_a_4025_,
    );
    lean_dec(v_a_4025_);
    lean_dec_ref(v_a_4024_);
    lean_dec(v_a_4023_);
    lean_dec_ref(v_a_4022_);
    return v_res_4027_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc(
    mut v_e_4028_: *mut LeanObject,
    mut v_a_4029_: *mut LeanObject,
    mut v_a_4030_: *mut LeanObject,
    mut v_a_4031_: *mut LeanObject,
    mut v_a_4032_: *mut LeanObject,
    mut v_a_4033_: *mut LeanObject,
    mut v_a_4034_: *mut LeanObject,
    mut v_a_4035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    v___x_4037_ =
        l_Lean_Meta_Sym_unfoldReducibleStep(v_e_4028_, v_a_4032_, v_a_4033_, v_a_4034_, v_a_4035_);
    return v___x_4037_;
}
pub unsafe fn l_Lean_Meta_Grind_unfoldReducibleSimproc___boxed(
    mut v_e_4038_: *mut LeanObject,
    mut v_a_4039_: *mut LeanObject,
    mut v_a_4040_: *mut LeanObject,
    mut v_a_4041_: *mut LeanObject,
    mut v_a_4042_: *mut LeanObject,
    mut v_a_4043_: *mut LeanObject,
    mut v_a_4044_: *mut LeanObject,
    mut v_a_4045_: *mut LeanObject,
    mut v_a_4046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4047_: *mut LeanObject = core::ptr::null_mut();
    v_res_4047_ = l_Lean_Meta_Grind_unfoldReducibleSimproc(
        v_e_4038_, v_a_4039_, v_a_4040_, v_a_4041_, v_a_4042_, v_a_4043_, v_a_4044_, v_a_4045_,
    );
    lean_dec(v_a_4045_);
    lean_dec_ref(v_a_4044_);
    lean_dec(v_a_4043_);
    lean_dec_ref(v_a_4042_);
    lean_dec(v_a_4041_);
    lean_dec_ref(v_a_4040_);
    lean_dec(v_a_4039_);
    return v_res_4047_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_(
    mut v___y_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
    mut v___y_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
    mut v___y_4054_: *mut LeanObject,
    mut v___y_4055_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Lean_Meta_Sym_unfoldReducibleStep(
        v___y_4048_,
        v___y_4052_,
        v___y_4053_,
        v___y_4054_,
        v___y_4055_,
    );
    return v___x_4057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed(
    mut v___y_4058_: *mut LeanObject,
    mut v___y_4059_: *mut LeanObject,
    mut v___y_4060_: *mut LeanObject,
    mut v___y_4061_: *mut LeanObject,
    mut v___y_4062_: *mut LeanObject,
    mut v___y_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4067_: *mut LeanObject = core::ptr::null_mut();
    v_res_4067_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___lam__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_(v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_, v___y_4064_, v___y_4065_);
    lean_dec(v___y_4065_);
    lean_dec_ref(v___y_4064_);
    lean_dec(v___y_4063_);
    lean_dec_ref(v___y_4062_);
    lean_dec(v___y_4061_);
    lean_dec_ref(v___y_4060_);
    lean_dec(v___y_4059_);
    return v_res_4067_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_()
-> *mut LeanObject {
    let mut v___f_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    v___f_4080_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__0_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4081_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4082_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__3_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
    v___x_4083_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4081_, v___x_4082_, v___f_4080_);
    return v___x_4083_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9____boxed(
    mut v_a_4084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4085_: *mut LeanObject = core::ptr::null_mut();
    v_res_4085_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_();
    return v_res_4085_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___redArg(
    mut v_a_4094_: *mut LeanObject,
    mut v_a_4095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: u8 = 0;
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: u8 = 0;
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut v_a_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4144_: u8 = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4148_: u8 = 0;
    let mut v_a_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4152_: u8 = 0;
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4156_: u8 = 0;
    let mut v_a_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4160_: u8 = 0;
    let mut v___x_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4164_: u8 = 0;
    let mut v_a_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4168_: u8 = 0;
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4172_: u8 = 0;
    let mut v_a_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4176_: u8 = 0;
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4180_: u8 = 0;
    let mut v_a_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4184_: u8 = 0;
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4188_: u8 = 0;
    let mut v_a_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4192_: u8 = 0;
    let mut v___x_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4196_: u8 = 0;
    let mut v_a_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4200_: u8 = 0;
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4204_: u8 = 0;
    let mut v_a_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4208_: u8 = 0;
    let mut v___x_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4212_: u8 = 0;
    let mut v_a_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4216_: u8 = 0;
    let mut v___x_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_a_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4097_ = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(v_a_4095_);
                if lean_obj_tag(v___x_4097_) == 0 {
                    v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
                    lean_inc(v_a_4098_);
                    lean_dec_ref_known(v___x_4097_, 1);
                    v___x_4099_ = l_Lean_Meta_Grind_getSimprocs___redArg___closed__2;
                    v___x_4100_ = l_Lean_Meta_Simp_Simprocs_erase(v_a_4098_, v___x_4099_);
                    v___x_4101_ = l_Lean_Meta_Grind_getSimprocs___redArg___closed__4;
                    v___x_4102_ = l_Lean_Meta_Simp_Simprocs_erase(v___x_4100_, v___x_4101_);
                    v___x_4103_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_;
                    v___x_4104_ = 1;
                    v___x_4105_ = l_Lean_Meta_Simp_Simprocs_add(
                        v___x_4102_,
                        v___x_4103_,
                        v___x_4104_,
                        v_a_4094_,
                        v_a_4095_,
                    );
                    if lean_obj_tag(v___x_4105_) == 0 {
                        v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
                        lean_inc(v_a_4106_);
                        lean_dec_ref_known(v___x_4105_, 1);
                        v___x_4107_ = l_Lean_Meta_Grind_addSimpMatchDiscrsOnly(
                            v_a_4106_, v_a_4094_, v_a_4095_,
                        );
                        if lean_obj_tag(v___x_4107_) == 0 {
                            v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
                            lean_inc(v_a_4108_);
                            lean_dec_ref_known(v___x_4107_, 1);
                            v___x_4109_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(
                                v_a_4108_, v_a_4094_, v_a_4095_,
                            );
                            if lean_obj_tag(v___x_4109_) == 0 {
                                v_a_4110_ = lean_ctor_get(v___x_4109_, 0);
                                lean_inc(v_a_4110_);
                                lean_dec_ref_known(v___x_4109_, 1);
                                v___x_4111_ = l_Lean_Meta_Grind_Arith_addSimproc(
                                    v_a_4110_, v_a_4094_, v_a_4095_,
                                );
                                if lean_obj_tag(v___x_4111_) == 0 {
                                    v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
                                    lean_inc(v_a_4112_);
                                    lean_dec_ref_known(v___x_4111_, 1);
                                    v___x_4113_ = l_Lean_Meta_Grind_addForallSimproc(
                                        v_a_4112_, v_a_4094_, v_a_4095_,
                                    );
                                    if lean_obj_tag(v___x_4113_) == 0 {
                                        v_a_4114_ = lean_ctor_get(v___x_4113_, 0);
                                        lean_inc(v_a_4114_);
                                        lean_dec_ref_known(v___x_4113_, 1);
                                        v___x_4115_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_;
                                        v___x_4116_ = l_Lean_Meta_Simp_Simprocs_add(
                                            v_a_4114_,
                                            v___x_4115_,
                                            v___x_4104_,
                                            v_a_4094_,
                                            v_a_4095_,
                                        );
                                        if lean_obj_tag(v___x_4116_) == 0 {
                                            v_a_4117_ = lean_ctor_get(v___x_4116_, 0);
                                            lean_inc(v_a_4117_);
                                            lean_dec_ref_known(v___x_4116_, 1);
                                            v___x_4118_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_;
                                            v___x_4119_ = l_Lean_Meta_Simp_Simprocs_add(
                                                v_a_4117_,
                                                v___x_4118_,
                                                v___x_4104_,
                                                v_a_4094_,
                                                v_a_4095_,
                                            );
                                            if lean_obj_tag(v___x_4119_) == 0 {
                                                v_a_4120_ = lean_ctor_get(v___x_4119_, 0);
                                                lean_inc(v_a_4120_);
                                                lean_dec_ref_known(v___x_4119_, 1);
                                                v___x_4121_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_;
                                                v___x_4122_ = l_Lean_Meta_Simp_Simprocs_add(
                                                    v_a_4120_,
                                                    v___x_4121_,
                                                    v___x_4104_,
                                                    v_a_4094_,
                                                    v_a_4095_,
                                                );
                                                if lean_obj_tag(v___x_4122_) == 0 {
                                                    v_a_4123_ = lean_ctor_get(v___x_4122_, 0);
                                                    lean_inc(v_a_4123_);
                                                    lean_dec_ref_known(v___x_4122_, 1);
                                                    v___x_4124_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21___closed__1_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_;
                                                    v___x_4125_ = 0;
                                                    v___x_4126_ = l_Lean_Meta_Simp_Simprocs_add(
                                                        v_a_4123_,
                                                        v___x_4124_,
                                                        v___x_4125_,
                                                        v_a_4094_,
                                                        v_a_4095_,
                                                    );
                                                    if lean_obj_tag(v___x_4126_) == 0 {
                                                        v_a_4127_ = lean_ctor_get(v___x_4126_, 0);
                                                        lean_inc(v_a_4127_);
                                                        lean_dec_ref_known(v___x_4126_, 1);
                                                        v___x_4128_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36___closed__2_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_;
                                                        v___x_4129_ = l_Lean_Meta_Simp_Simprocs_add(
                                                            v_a_4127_,
                                                            v___x_4128_,
                                                            v___x_4125_,
                                                            v_a_4094_,
                                                            v_a_4095_,
                                                        );
                                                        if lean_obj_tag(v___x_4129_) == 0 {
                                                            v_a_4130_ =
                                                                lean_ctor_get(v___x_4129_, 0);
                                                            v_isSharedCheck_4140_ =
                                                                (!lean_is_exclusive(v___x_4129_))
                                                                    as u8;
                                                            if v_isSharedCheck_4140_ == 0 {
                                                                v___x_4132_ = v___x_4129_;
                                                                v_isShared_4133_ =
                                                                    v_isSharedCheck_4140_;
                                                                state = 1;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4130_);
                                                                lean_dec(v___x_4129_);
                                                                v___x_4132_ = lean_box(0);
                                                                v_isShared_4133_ =
                                                                    v_isSharedCheck_4140_;
                                                                state = 1;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_4141_ =
                                                                lean_ctor_get(v___x_4129_, 0);
                                                            v_isSharedCheck_4148_ =
                                                                (!lean_is_exclusive(v___x_4129_))
                                                                    as u8;
                                                            if v_isSharedCheck_4148_ == 0 {
                                                                v___x_4143_ = v___x_4129_;
                                                                v_isShared_4144_ =
                                                                    v_isSharedCheck_4148_;
                                                                state = 3;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4141_);
                                                                lean_dec(v___x_4129_);
                                                                v___x_4143_ = lean_box(0);
                                                                v_isShared_4144_ =
                                                                    v_isSharedCheck_4148_;
                                                                state = 3;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        v_a_4149_ = lean_ctor_get(v___x_4126_, 0);
                                                        v_isSharedCheck_4156_ =
                                                            (!lean_is_exclusive(v___x_4126_)) as u8;
                                                        if v_isSharedCheck_4156_ == 0 {
                                                            v___x_4151_ = v___x_4126_;
                                                            v_isShared_4152_ =
                                                                v_isSharedCheck_4156_;
                                                            state = 5;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_4149_);
                                                            lean_dec(v___x_4126_);
                                                            v___x_4151_ = lean_box(0);
                                                            v_isShared_4152_ =
                                                                v_isSharedCheck_4156_;
                                                            state = 5;
                                                            continue;
                                                        }
                                                    }
                                                } else {
                                                    v_a_4157_ = lean_ctor_get(v___x_4122_, 0);
                                                    v_isSharedCheck_4164_ =
                                                        (!lean_is_exclusive(v___x_4122_)) as u8;
                                                    if v_isSharedCheck_4164_ == 0 {
                                                        v___x_4159_ = v___x_4122_;
                                                        v_isShared_4160_ = v_isSharedCheck_4164_;
                                                        state = 7;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_4157_);
                                                        lean_dec(v___x_4122_);
                                                        v___x_4159_ = lean_box(0);
                                                        v_isShared_4160_ = v_isSharedCheck_4164_;
                                                        state = 7;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                v_a_4165_ = lean_ctor_get(v___x_4119_, 0);
                                                v_isSharedCheck_4172_ =
                                                    (!lean_is_exclusive(v___x_4119_)) as u8;
                                                if v_isSharedCheck_4172_ == 0 {
                                                    v___x_4167_ = v___x_4119_;
                                                    v_isShared_4168_ = v_isSharedCheck_4172_;
                                                    state = 9;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_4165_);
                                                    lean_dec(v___x_4119_);
                                                    v___x_4167_ = lean_box(0);
                                                    v_isShared_4168_ = v_isSharedCheck_4172_;
                                                    state = 9;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            v_a_4173_ = lean_ctor_get(v___x_4116_, 0);
                                            v_isSharedCheck_4180_ =
                                                (!lean_is_exclusive(v___x_4116_)) as u8;
                                            if v_isSharedCheck_4180_ == 0 {
                                                v___x_4175_ = v___x_4116_;
                                                v_isShared_4176_ = v_isSharedCheck_4180_;
                                                state = 11;
                                                continue;
                                            } else {
                                                lean_inc(v_a_4173_);
                                                lean_dec(v___x_4116_);
                                                v___x_4175_ = lean_box(0);
                                                v_isShared_4176_ = v_isSharedCheck_4180_;
                                                state = 11;
                                                continue;
                                            }
                                        }
                                    } else {
                                        v_a_4181_ = lean_ctor_get(v___x_4113_, 0);
                                        v_isSharedCheck_4188_ =
                                            (!lean_is_exclusive(v___x_4113_)) as u8;
                                        if v_isSharedCheck_4188_ == 0 {
                                            v___x_4183_ = v___x_4113_;
                                            v_isShared_4184_ = v_isSharedCheck_4188_;
                                            state = 13;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4181_);
                                            lean_dec(v___x_4113_);
                                            v___x_4183_ = lean_box(0);
                                            v_isShared_4184_ = v_isSharedCheck_4188_;
                                            state = 13;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_a_4189_ = lean_ctor_get(v___x_4111_, 0);
                                    v_isSharedCheck_4196_ = (!lean_is_exclusive(v___x_4111_)) as u8;
                                    if v_isSharedCheck_4196_ == 0 {
                                        v___x_4191_ = v___x_4111_;
                                        v_isShared_4192_ = v_isSharedCheck_4196_;
                                        state = 15;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4189_);
                                        lean_dec(v___x_4111_);
                                        v___x_4191_ = lean_box(0);
                                        v_isShared_4192_ = v_isSharedCheck_4196_;
                                        state = 15;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_4197_ = lean_ctor_get(v___x_4109_, 0);
                                v_isSharedCheck_4204_ = (!lean_is_exclusive(v___x_4109_)) as u8;
                                if v_isSharedCheck_4204_ == 0 {
                                    v___x_4199_ = v___x_4109_;
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_4197_);
                                    lean_dec(v___x_4109_);
                                    v___x_4199_ = lean_box(0);
                                    v_isShared_4200_ = v_isSharedCheck_4204_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            v_a_4205_ = lean_ctor_get(v___x_4107_, 0);
                            v_isSharedCheck_4212_ = (!lean_is_exclusive(v___x_4107_)) as u8;
                            if v_isSharedCheck_4212_ == 0 {
                                v___x_4207_ = v___x_4107_;
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 19;
                                continue;
                            } else {
                                lean_inc(v_a_4205_);
                                lean_dec(v___x_4107_);
                                v___x_4207_ = lean_box(0);
                                v_isShared_4208_ = v_isSharedCheck_4212_;
                                state = 19;
                                continue;
                            }
                        }
                    } else {
                        v_a_4213_ = lean_ctor_get(v___x_4105_, 0);
                        v_isSharedCheck_4220_ = (!lean_is_exclusive(v___x_4105_)) as u8;
                        if v_isSharedCheck_4220_ == 0 {
                            v___x_4215_ = v___x_4105_;
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 21;
                            continue;
                        } else {
                            lean_inc(v_a_4213_);
                            lean_dec(v___x_4105_);
                            v___x_4215_ = lean_box(0);
                            v_isShared_4216_ = v_isSharedCheck_4220_;
                            state = 21;
                            continue;
                        }
                    }
                } else {
                    v_a_4221_ = lean_ctor_get(v___x_4097_, 0);
                    v_isSharedCheck_4228_ = (!lean_is_exclusive(v___x_4097_)) as u8;
                    if v_isSharedCheck_4228_ == 0 {
                        v___x_4223_ = v___x_4097_;
                        v_isShared_4224_ = v_isSharedCheck_4228_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_4221_);
                        lean_dec(v___x_4097_);
                        v___x_4223_ = lean_box(0);
                        v_isShared_4224_ = v_isSharedCheck_4228_;
                        state = 23;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4134_ = lean_unsigned_to_nat(1);
                v___x_4135_ = lean_mk_empty_array_with_capacity(v___x_4134_);
                v___x_4136_ = lean_array_push(v___x_4135_, v_a_4130_);
                if v_isShared_4133_ == 0 {
                    lean_ctor_set(v___x_4132_, 0, v___x_4136_);
                    v___x_4138_ = v___x_4132_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4138_;
            }
            3 => {
                if v_isShared_4144_ == 0 {
                    v___x_4146_ = v___x_4143_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4147_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4147_, 0, v_a_4141_);
                    v___x_4146_ = v_reuseFailAlloc_4147_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4146_;
            }
            5 => {
                if v_isShared_4152_ == 0 {
                    v___x_4154_ = v___x_4151_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
                    v___x_4154_ = v_reuseFailAlloc_4155_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4154_;
            }
            7 => {
                if v_isShared_4160_ == 0 {
                    v___x_4162_ = v___x_4159_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
                    v___x_4162_ = v_reuseFailAlloc_4163_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4162_;
            }
            9 => {
                if v_isShared_4168_ == 0 {
                    v___x_4170_ = v___x_4167_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
                    v___x_4170_ = v_reuseFailAlloc_4171_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4170_;
            }
            11 => {
                if v_isShared_4176_ == 0 {
                    v___x_4178_ = v___x_4175_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4179_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4179_, 0, v_a_4173_);
                    v___x_4178_ = v_reuseFailAlloc_4179_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4178_;
            }
            13 => {
                if v_isShared_4184_ == 0 {
                    v___x_4186_ = v___x_4183_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4187_, 0, v_a_4181_);
                    v___x_4186_ = v_reuseFailAlloc_4187_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4186_;
            }
            15 => {
                if v_isShared_4192_ == 0 {
                    v___x_4194_ = v___x_4191_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4195_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4195_, 0, v_a_4189_);
                    v___x_4194_ = v_reuseFailAlloc_4195_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4194_;
            }
            17 => {
                if v_isShared_4200_ == 0 {
                    v___x_4202_ = v___x_4199_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4203_, 0, v_a_4197_);
                    v___x_4202_ = v_reuseFailAlloc_4203_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4202_;
            }
            19 => {
                if v_isShared_4208_ == 0 {
                    v___x_4210_ = v___x_4207_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4211_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4211_, 0, v_a_4205_);
                    v___x_4210_ = v_reuseFailAlloc_4211_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4210_;
            }
            21 => {
                if v_isShared_4216_ == 0 {
                    v___x_4218_ = v___x_4215_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4213_);
                    v___x_4218_ = v_reuseFailAlloc_4219_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4218_;
            }
            23 => {
                if v_isShared_4224_ == 0 {
                    v___x_4226_ = v___x_4223_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
                    v___x_4226_ = v_reuseFailAlloc_4227_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4226_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___redArg___boxed(
    mut v_a_4229_: *mut LeanObject,
    mut v_a_4230_: *mut LeanObject,
    mut v_a_4231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4232_: *mut LeanObject = core::ptr::null_mut();
    v_res_4232_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4229_, v_a_4230_);
    lean_dec(v_a_4230_);
    lean_dec_ref(v_a_4229_);
    return v_res_4232_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs(
    mut v_a_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
    mut v_a_4235_: *mut LeanObject,
    mut v_a_4236_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    v___x_4238_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4235_, v_a_4236_);
    return v___x_4238_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimprocs___boxed(
    mut v_a_4239_: *mut LeanObject,
    mut v_a_4240_: *mut LeanObject,
    mut v_a_4241_: *mut LeanObject,
    mut v_a_4242_: *mut LeanObject,
    mut v_a_4243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4244_: *mut LeanObject = core::ptr::null_mut();
    v_res_4244_ = l_Lean_Meta_Grind_getSimprocs(v_a_4239_, v_a_4240_, v_a_4241_, v_a_4242_);
    lean_dec(v_a_4242_);
    lean_dec_ref(v_a_4241_);
    lean_dec(v_a_4240_);
    lean_dec_ref(v_a_4239_);
    return v_res_4244_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
    mut v_s_4245_: *mut LeanObject,
    mut v_declName_4246_: *mut LeanObject,
    mut v_a_4247_: *mut LeanObject,
    mut v_a_4248_: *mut LeanObject,
    mut v_a_4249_: *mut LeanObject,
    mut v_a_4250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: u8 = 0;
    let mut v___x_4255_: u8 = 0;
    v___x_4252_ = lean_st_ref_get(v_a_4250_);
    v_env_4253_ = lean_ctor_get(v___x_4252_, 0);
    lean_inc_ref(v_env_4253_);
    lean_dec(v___x_4252_);
    v___x_4254_ = 1;
    lean_inc(v_declName_4246_);
    v___x_4255_ = l_Lean_Environment_contains(v_env_4253_, v_declName_4246_, v___x_4254_);
    if v___x_4255_ == 0 {
        let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_declName_4246_);
        v___x_4256_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_4256_, 0, v_s_4245_);
        return v___x_4256_;
    } else {
        let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
        v___x_4257_ = l_Lean_Meta_SimpTheorems_addDeclToUnfold(
            v_s_4245_,
            v_declName_4246_,
            v_a_4247_,
            v_a_4248_,
            v_a_4249_,
            v_a_4250_,
        );
        return v___x_4257_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold___boxed(
    mut v_s_4258_: *mut LeanObject,
    mut v_declName_4259_: *mut LeanObject,
    mut v_a_4260_: *mut LeanObject,
    mut v_a_4261_: *mut LeanObject,
    mut v_a_4262_: *mut LeanObject,
    mut v_a_4263_: *mut LeanObject,
    mut v_a_4264_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4265_: *mut LeanObject = core::ptr::null_mut();
    v_res_4265_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
        v_s_4258_,
        v_declName_4259_,
        v_a_4260_,
        v_a_4261_,
        v_a_4262_,
        v_a_4263_,
    );
    lean_dec(v_a_4263_);
    lean_dec_ref(v_a_4262_);
    lean_dec(v_a_4261_);
    lean_dec_ref(v_a_4260_);
    return v_res_4265_;
}
pub unsafe fn l_Lean_Meta_Grind_getNormTheorems(
    mut v_a_4287_: *mut LeanObject,
    mut v_a_4288_: *mut LeanObject,
    mut v_a_4289_: *mut LeanObject,
    mut v_a_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_Meta_Grind_normExt;
    v___x_4293_ = l_Lean_Meta_SimpExtension_getTheorems___redArg(v___x_4292_, v_a_4290_);
    if lean_obj_tag(v___x_4293_) == 0 {
        let mut v_a_4294_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
        v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
        lean_inc(v_a_4294_);
        lean_dec_ref_known(v___x_4293_, 1);
        v___x_4295_ = l_Lean_Meta_Grind_getNormTheorems___closed__2;
        v___x_4296_ =
            l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
                v_a_4294_,
                v___x_4295_,
                v_a_4287_,
                v_a_4288_,
                v_a_4289_,
                v_a_4290_,
            );
        if lean_obj_tag(v___x_4296_) == 0 {
            let mut v_a_4297_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4299_: *mut LeanObject = core::ptr::null_mut();
            v_a_4297_ = lean_ctor_get(v___x_4296_, 0);
            lean_inc(v_a_4297_);
            lean_dec_ref_known(v___x_4296_, 1);
            v___x_4298_ = l_Lean_Meta_Grind_getNormTheorems___closed__5;
            v___x_4299_ =
                l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
                    v_a_4297_,
                    v___x_4298_,
                    v_a_4287_,
                    v_a_4288_,
                    v_a_4289_,
                    v_a_4290_,
                );
            if lean_obj_tag(v___x_4299_) == 0 {
                let mut v_a_4300_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
                v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
                lean_inc(v_a_4300_);
                lean_dec_ref_known(v___x_4299_, 1);
                v___x_4301_ = l_Lean_Meta_Grind_getNormTheorems___closed__7;
                v___x_4302_ =
                    l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(
                        v_a_4300_,
                        v___x_4301_,
                        v_a_4287_,
                        v_a_4288_,
                        v_a_4289_,
                        v_a_4290_,
                    );
                if lean_obj_tag(v___x_4302_) == 0 {
                    let mut v_a_4303_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4304_: *mut LeanObject = core::ptr::null_mut();
                    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
                    v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
                    lean_inc(v_a_4303_);
                    lean_dec_ref_known(v___x_4302_, 1);
                    v___x_4304_ = l_Lean_Meta_Grind_getNormTheorems___closed__9;
                    v___x_4305_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_4303_, v___x_4304_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
                    if lean_obj_tag(v___x_4305_) == 0 {
                        let mut v_a_4306_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4307_: *mut LeanObject = core::ptr::null_mut();
                        let mut v___x_4308_: *mut LeanObject = core::ptr::null_mut();
                        v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
                        lean_inc(v_a_4306_);
                        lean_dec_ref_known(v___x_4305_, 1);
                        v___x_4307_ = l_Lean_Meta_Grind_getNormTheorems___closed__11;
                        v___x_4308_ = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0__Lean_Meta_Grind_addDeclToUnfold(v_a_4306_, v___x_4307_, v_a_4287_, v_a_4288_, v_a_4289_, v_a_4290_);
                        return v___x_4308_;
                    } else {
                        return v___x_4305_;
                    }
                } else {
                    return v___x_4302_;
                }
            } else {
                return v___x_4299_;
            }
        } else {
            return v___x_4296_;
        }
    } else {
        return v___x_4293_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_getNormTheorems___boxed(
    mut v_a_4309_: *mut LeanObject,
    mut v_a_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v_a_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4314_: *mut LeanObject = core::ptr::null_mut();
    v_res_4314_ = l_Lean_Meta_Grind_getNormTheorems(v_a_4309_, v_a_4310_, v_a_4311_, v_a_4312_);
    lean_dec(v_a_4312_);
    lean_dec_ref(v_a_4311_);
    lean_dec(v_a_4310_);
    lean_dec_ref(v_a_4309_);
    return v_res_4314_;
}
pub unsafe fn l_Lean_Meta_Grind_getSimpContext(
    mut v_config_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
    mut v_a_4317_: *mut LeanObject,
    mut v_a_4318_: *mut LeanObject,
    mut v_a_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDelta_4325_: u8 = 0;
    let mut v_zeta_4326_: u8 = 0;
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: u8 = 0;
    let mut v___x_4330_: u8 = 0;
    let mut v___x_4331_: u8 = 0;
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4342_: u8 = 0;
    let mut v___x_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_a_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4350_: u8 = 0;
    let mut v___x_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4321_ =
                    l_Lean_Meta_Grind_getNormTheorems(v_a_4316_, v_a_4317_, v_a_4318_, v_a_4319_);
                if lean_obj_tag(v___x_4321_) == 0 {
                    v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
                    lean_inc(v_a_4322_);
                    lean_dec_ref_known(v___x_4321_, 1);
                    v___x_4323_ = l_Lean_Meta_getSimpCongrTheorems___redArg(v_a_4319_);
                    if lean_obj_tag(v___x_4323_) == 0 {
                        v_a_4324_ = lean_ctor_get(v___x_4323_, 0);
                        lean_inc(v_a_4324_);
                        lean_dec_ref_known(v___x_4323_, 1);
                        v_zetaDelta_4325_ = lean_ctor_get_uint8(
                            v_config_4315_,
                            (core::mem::size_of::<*mut LeanObject>() * 13 + 19) as u32,
                        );
                        v_zeta_4326_ = lean_ctor_get_uint8(
                            v_config_4315_,
                            (core::mem::size_of::<*mut LeanObject>() * 13 + 20) as u32,
                        );
                        v___x_4327_ = lean_unsigned_to_nat(100000);
                        v___x_4328_ = lean_unsigned_to_nat(2);
                        v___x_4329_ = 0;
                        v___x_4330_ = 1;
                        v___x_4331_ = 0;
                        v___x_4332_ = lean_box(0);
                        v___x_4333_ = lean_alloc_ctor(0, 3, (29) as u32);
                        lean_ctor_set(v___x_4333_, 0, v___x_4327_);
                        lean_ctor_set(v___x_4333_, 1, v___x_4328_);
                        lean_ctor_set(v___x_4333_, 2, v___x_4332_);
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 3) as u32,
                            v_zeta_4326_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 4) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 5) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 6) as u32,
                            v___x_4331_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 7) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 9) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 10) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 11) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 12) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 13) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 14) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 15) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                            v_zetaDelta_4325_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 17) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 18) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 19) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 20) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 21) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 22) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 23) as u32,
                            v___x_4330_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 24) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 25) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 26) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 27) as u32,
                            v___x_4329_,
                        );
                        lean_ctor_set_uint8(
                            v___x_4333_,
                            (core::mem::size_of::<*mut LeanObject>() * 3 + 28) as u32,
                            v___x_4329_,
                        );
                        v___x_4334_ = lean_unsigned_to_nat(1);
                        v___x_4335_ = lean_mk_empty_array_with_capacity(v___x_4334_);
                        v___x_4336_ = lean_array_push(v___x_4335_, v_a_4322_);
                        v___x_4337_ = l_Lean_Options_empty;
                        v___x_4338_ = l_Lean_Meta_Simp_mkContext___redArg(
                            v___x_4333_,
                            v___x_4336_,
                            v_a_4324_,
                            v___x_4337_,
                            v_a_4316_,
                            v_a_4318_,
                            v_a_4319_,
                        );
                        return v___x_4338_;
                    } else {
                        lean_dec(v_a_4322_);
                        v_a_4339_ = lean_ctor_get(v___x_4323_, 0);
                        v_isSharedCheck_4346_ = (!lean_is_exclusive(v___x_4323_)) as u8;
                        if v_isSharedCheck_4346_ == 0 {
                            v___x_4341_ = v___x_4323_;
                            v_isShared_4342_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4339_);
                            lean_dec(v___x_4323_);
                            v___x_4341_ = lean_box(0);
                            v_isShared_4342_ = v_isSharedCheck_4346_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_a_4347_ = lean_ctor_get(v___x_4321_, 0);
                    v_isSharedCheck_4354_ = (!lean_is_exclusive(v___x_4321_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4349_ = v___x_4321_;
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4347_);
                        lean_dec(v___x_4321_);
                        v___x_4349_ = lean_box(0);
                        v_isShared_4350_ = v_isSharedCheck_4354_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4342_ == 0 {
                    v___x_4344_ = v___x_4341_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
                    v___x_4344_ = v_reuseFailAlloc_4345_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4344_;
            }
            3 => {
                if v_isShared_4350_ == 0 {
                    v___x_4352_ = v___x_4349_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4353_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4353_, 0, v_a_4347_);
                    v___x_4352_ = v_reuseFailAlloc_4353_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getSimpContext___boxed(
    mut v_config_4355_: *mut LeanObject,
    mut v_a_4356_: *mut LeanObject,
    mut v_a_4357_: *mut LeanObject,
    mut v_a_4358_: *mut LeanObject,
    mut v_a_4359_: *mut LeanObject,
    mut v_a_4360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4361_: *mut LeanObject = core::ptr::null_mut();
    v_res_4361_ = l_Lean_Meta_Grind_getSimpContext(
        v_config_4355_,
        v_a_4356_,
        v_a_4357_,
        v_a_4358_,
        v_a_4359_,
    );
    lean_dec(v_a_4359_);
    lean_dec_ref(v_a_4358_);
    lean_dec(v_a_4357_);
    lean_dec_ref(v_a_4356_);
    lean_dec_ref(v_config_4355_);
    return v_res_4361_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__0() -> *mut LeanObject {
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    v___x_4362_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4362_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__1() -> *mut LeanObject {
    let mut v___x_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    v___x_4363_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__0_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__0,
    );
    v___x_4364_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4364_, 0, v___x_4363_);
    return v___x_4364_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__2() -> *mut LeanObject {
    let mut v___x_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    v___x_4365_ = lean_unsigned_to_nat(0);
    v___x_4366_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__1,
    );
    v___x_4367_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4367_, 0, v___x_4366_);
    lean_ctor_set(v___x_4367_, 1, v___x_4365_);
    return v___x_4367_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__3() -> *mut LeanObject {
    let mut v___x_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut LeanObject = core::ptr::null_mut();
    v___x_4368_ = lean_unsigned_to_nat(32);
    v___x_4369_ = lean_mk_empty_array_with_capacity(v___x_4368_);
    v___x_4370_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4370_, 0, v___x_4369_);
    return v___x_4370_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__4() -> *mut LeanObject {
    let mut v___x_4371_: usize = 0;
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    v___x_4371_ = 5usize;
    v___x_4372_ = lean_unsigned_to_nat(0);
    v___x_4373_ = lean_unsigned_to_nat(32);
    v___x_4374_ = lean_mk_empty_array_with_capacity(v___x_4373_);
    v___x_4375_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__3_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__3,
    );
    v___x_4376_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_4376_, 0, v___x_4375_);
    lean_ctor_set(v___x_4376_, 1, v___x_4374_);
    lean_ctor_set(v___x_4376_, 2, v___x_4372_);
    lean_ctor_set(v___x_4376_, 3, v___x_4372_);
    lean_ctor_set_usize(v___x_4376_, 4, v___x_4371_);
    return v___x_4376_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__5() -> *mut LeanObject {
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut LeanObject = core::ptr::null_mut();
    v___x_4377_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__4_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__4,
    );
    v___x_4378_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__1_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__1,
    );
    v___x_4379_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4379_, 0, v___x_4378_);
    lean_ctor_set(v___x_4379_, 1, v___x_4378_);
    lean_ctor_set(v___x_4379_, 2, v___x_4378_);
    lean_ctor_set(v___x_4379_, 3, v___x_4377_);
    return v___x_4379_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_normalizeImp___closed__6() -> *mut LeanObject {
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut LeanObject = core::ptr::null_mut();
    v___x_4380_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__5_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__5,
    );
    v___x_4381_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__2_once),
        _init_l_Lean_Meta_Grind_normalizeImp___closed__2,
    );
    v___x_4382_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4382_, 0, v___x_4381_);
    lean_ctor_set(v___x_4382_, 1, v___x_4380_);
    return v___x_4382_;
}
pub unsafe fn lean_grind_normalize(
    mut v_e_4383_: *mut LeanObject,
    mut v_config_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
    mut v_a_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
    mut v_a_4388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4400_: u8 = 0;
    let mut v_fst_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4406_: u8 = 0;
    let mut v_a_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4414_: u8 = 0;
    let mut v_a_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4418_: u8 = 0;
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4422_: u8 = 0;
    let mut v_a_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4390_ = l_Lean_Meta_Grind_getSimpContext(
                    v_config_4384_,
                    v_a_4385_,
                    v_a_4386_,
                    v_a_4387_,
                    v_a_4388_,
                );
                lean_dec_ref(v_config_4384_);
                if lean_obj_tag(v___x_4390_) == 0 {
                    v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
                    lean_inc(v_a_4391_);
                    lean_dec_ref_known(v___x_4390_, 1);
                    v___x_4392_ = l_Lean_Meta_Grind_getSimprocs___redArg(v_a_4387_, v_a_4388_);
                    if lean_obj_tag(v___x_4392_) == 0 {
                        v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
                        lean_inc(v_a_4393_);
                        lean_dec_ref_known(v___x_4392_, 1);
                        v___x_4394_ = lean_box(0);
                        v___x_4395_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Meta_Grind_normalizeImp___closed__6),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Grind_normalizeImp___closed__6_once
                            ),
                            _init_l_Lean_Meta_Grind_normalizeImp___closed__6,
                        );
                        v___x_4396_ = l_Lean_Meta_simp(
                            v_e_4383_,
                            v_a_4391_,
                            v_a_4393_,
                            v___x_4394_,
                            v___x_4395_,
                            v_a_4385_,
                            v_a_4386_,
                            v_a_4387_,
                            v_a_4388_,
                        );
                        lean_dec(v_a_4388_);
                        lean_dec_ref(v_a_4387_);
                        lean_dec(v_a_4386_);
                        lean_dec_ref(v_a_4385_);
                        if lean_obj_tag(v___x_4396_) == 0 {
                            v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
                            v_isSharedCheck_4406_ = (!lean_is_exclusive(v___x_4396_)) as u8;
                            if v_isSharedCheck_4406_ == 0 {
                                v___x_4399_ = v___x_4396_;
                                v_isShared_4400_ = v_isSharedCheck_4406_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4397_);
                                lean_dec(v___x_4396_);
                                v___x_4399_ = lean_box(0);
                                v_isShared_4400_ = v_isSharedCheck_4406_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_4407_ = lean_ctor_get(v___x_4396_, 0);
                            v_isSharedCheck_4414_ = (!lean_is_exclusive(v___x_4396_)) as u8;
                            if v_isSharedCheck_4414_ == 0 {
                                v___x_4409_ = v___x_4396_;
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_4407_);
                                lean_dec(v___x_4396_);
                                v___x_4409_ = lean_box(0);
                                v_isShared_4410_ = v_isSharedCheck_4414_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4391_);
                        lean_dec(v_a_4388_);
                        lean_dec_ref(v_a_4387_);
                        lean_dec(v_a_4386_);
                        lean_dec_ref(v_a_4385_);
                        lean_dec_ref(v_e_4383_);
                        v_a_4415_ = lean_ctor_get(v___x_4392_, 0);
                        v_isSharedCheck_4422_ = (!lean_is_exclusive(v___x_4392_)) as u8;
                        if v_isSharedCheck_4422_ == 0 {
                            v___x_4417_ = v___x_4392_;
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_4415_);
                            lean_dec(v___x_4392_);
                            v___x_4417_ = lean_box(0);
                            v_isShared_4418_ = v_isSharedCheck_4422_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_4388_);
                    lean_dec_ref(v_a_4387_);
                    lean_dec(v_a_4386_);
                    lean_dec_ref(v_a_4385_);
                    lean_dec_ref(v_e_4383_);
                    v_a_4423_ = lean_ctor_get(v___x_4390_, 0);
                    v_isSharedCheck_4430_ = (!lean_is_exclusive(v___x_4390_)) as u8;
                    if v_isSharedCheck_4430_ == 0 {
                        v___x_4425_ = v___x_4390_;
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4423_);
                        lean_dec(v___x_4390_);
                        v___x_4425_ = lean_box(0);
                        v_isShared_4426_ = v_isSharedCheck_4430_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4401_ = lean_ctor_get(v_a_4397_, 0);
                lean_inc(v_fst_4401_);
                lean_dec(v_a_4397_);
                v_expr_4402_ = lean_ctor_get(v_fst_4401_, 0);
                lean_inc_ref(v_expr_4402_);
                lean_dec(v_fst_4401_);
                if v_isShared_4400_ == 0 {
                    lean_ctor_set(v___x_4399_, 0, v_expr_4402_);
                    v___x_4404_ = v___x_4399_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_expr_4402_);
                    v___x_4404_ = v_reuseFailAlloc_4405_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4404_;
            }
            3 => {
                if v_isShared_4410_ == 0 {
                    v___x_4412_ = v___x_4409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
                    v___x_4412_ = v_reuseFailAlloc_4413_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4412_;
            }
            5 => {
                if v_isShared_4418_ == 0 {
                    v___x_4420_ = v___x_4417_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
                    v___x_4420_ = v_reuseFailAlloc_4421_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4420_;
            }
            7 => {
                if v_isShared_4426_ == 0 {
                    v___x_4428_ = v___x_4425_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
                    v___x_4428_ = v_reuseFailAlloc_4429_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4428_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_normalizeImp___boxed(
    mut v_e_4431_: *mut LeanObject,
    mut v_config_4432_: *mut LeanObject,
    mut v_a_4433_: *mut LeanObject,
    mut v_a_4434_: *mut LeanObject,
    mut v_a_4435_: *mut LeanObject,
    mut v_a_4436_: *mut LeanObject,
    mut v_a_4437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4438_: *mut LeanObject = core::ptr::null_mut();
    v_res_4438_ = lean_grind_normalize(
        v_e_4431_,
        v_config_4432_,
        v_a_4433_,
        v_a_4434_,
        v_a_4435_,
        v_a_4436_,
    );
    return v_res_4438_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Norm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpEq_declare__11_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3241500959____hygCtx___hyg_12_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpDIte_declare__16_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_2954503720____hygCtx___hyg_13_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_pushNot_declare__21_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3137565202____hygCtx___hyg_10_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_simpOr_declare__26_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_902628210____hygCtx___hyg_11_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_reduceCtorEqCheap_declare__31_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_3634819044____hygCtx___hyg_13_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Grind_SimpUtil_0____regBuiltin_Lean_Meta_Grind_unfoldReducibleSimproc_declare__36_00___x40_Lean_Meta_Tactic_Grind_SimpUtil_1981575202____hygCtx___hyg_9_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_MatchDiscrOnly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_ForallProp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs_Core(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Norm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Config(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_SimpUtil(builtin);
}
