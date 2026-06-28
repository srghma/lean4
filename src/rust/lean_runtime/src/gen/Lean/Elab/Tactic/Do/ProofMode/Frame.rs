// Lean compiler output
// Module: Lean.Elab.Tactic.Do.ProofMode.Frame
// Imports: Std.Tactic.Do.Syntax Lean.Elab.Tactic.Do.ProofMode.Focus
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
    l_Lean_Name_mkStr6, l_Lean_Name_num___override,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Elab::Tactic::Basic::{
    l_Lean_Elab_Tactic_getMainGoal___redArg, l_Lean_Elab_Tactic_replaceMainGoal___redArg,
    l_Lean_Elab_Tactic_tacticElabAttribute,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::Focus::{
    initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
    runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus,
};
use crate::r#gen::Lean::Elab::Tactic::Do::ProofMode::MGoal::{
    l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr, l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr,
    l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21, l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f,
    l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f, l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_hasMVar, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkApp4, l_Lean_mkApp7,
    l_Lean_mkConst, l_Lean_mkSort,
};
use crate::r#gen::Lean::KeyedDeclsAttribute::l_Lean_KeyedDeclsAttribute_addBuiltin___redArg;
use crate::r#gen::Lean::Message::l_Lean_stringToMessageData;
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp,
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed,
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isDefEq___boxed,
    l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar, l_Lean_Meta_mkFreshExprMVar___boxed,
    l_Lean_Meta_mkLambdaFVars, l_Lean_Meta_mkLambdaFVars___boxed,
    l_Lean_Meta_withLocalDeclD___redArg,
};
use crate::r#gen::Lean::Meta::SynthInstance::{
    l_Lean_Meta_trySynthInstance, l_Lean_Meta_trySynthInstance___boxed,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    l_Lean_MVarId_getType, l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
use crate::r#gen::Std::Tactic::Do::Syntax::{
    initialize_Std_Tactic_Do_Syntax, runtime_initialize_Std_Tactic_Do_Syntax,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt, lean_panic_fn_borrowed,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_apply_9, lean_apply_10,
    lean_apply_12, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
pub static l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 0, m_objs: [] };
static mut l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [104, 0]};
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__0_value) as *mut LeanObject,8738205681931236784 as *mut LeanObject] };
static mut l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0_value: LeanStringObject<36> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 70, 114, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1_value: LeanStringObject<100> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 100, m_capacity: 100, m_length: 99, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 70, 114, 97, 109, 101, 46, 48, 46, 76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 84, 97, 99, 116, 105, 99, 46, 68, 111, 46, 80, 114, 111, 111, 102, 77, 111, 100, 101, 46, 116, 114, 97, 110, 115, 102, 101, 114, 72, 121, 112, 78, 97, 109, 101, 115, 46, 108, 97, 98, 101, 108, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [70, 114, 97, 109, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [102, 114, 97, 109, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0_value: LeanClosureObject<1> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1_value) as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0_value:
    LeanStringObject<5> = LeanStringObject {
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
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__0_value
        ) as *mut LeanObject,
        11870096045526947150 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value:
    LeanStringObject<7> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [72, 97, 115, 70, 114, 97, 109, 101, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value:
    LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 116, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value:
    LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [68, 111, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value
) as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value:
    LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [83, 80, 114, 101, 100, 0],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value
) as *mut LeanObject;
static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_0:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value
        ) as *mut LeanObject,
        15734321041234825264 as *mut LeanObject,
    ],
};
static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_1:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_0
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value
        ) as *mut LeanObject,
        7300584325018775040 as *mut LeanObject,
    ],
};
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value
        ) as *mut LeanObject,
        13332341187416043682 as *mut LeanObject,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0_value:
    LeanStringObject<22> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 22,
    m_capacity: 22,
    m_length: 21,
    m_data: [
        67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 105, 110, 102, 101, 114, 32, 102, 114, 97,
        109, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value) as *mut LeanObject,7300584325018775040 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2_value) as *mut LeanObject,13332341187416043682 as *mut LeanObject] };
static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value) as *mut LeanObject,18104247681175793831 as *mut LeanObject] };
pub static l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1_value) as *mut LeanObject,6311446840719414380 as *mut LeanObject] };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0_value) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        110, 111, 116, 32, 105, 110, 32, 112, 114, 111, 111, 102, 32, 109, 111, 100, 101, 0,
    ],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0_value
) as *mut LeanObject;
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 9,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1_value)
        as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 114, 115, 101, 114, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [109, 102, 114, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__1_value) as *mut LeanObject,8018486133748762727 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value) as *mut LeanObject,18344149449936419494 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__2_value) as *mut LeanObject,13469542834647568846 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [69, 108, 97, 98, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [80, 114, 111, 111, 102, 77, 111, 100, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [101, 108, 97, 98, 77, 70, 114, 97, 109, 101, 0]};
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6_value) as *mut LeanObject;
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__4_value) as *mut LeanObject,11510100434945111860 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0_value) as *mut LeanObject,12733524109236233889 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1_value) as *mut LeanObject,11384710337598098789 as *mut LeanObject] };
static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_4: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__5_value) as *mut LeanObject,5427134421608450815 as *mut LeanObject] };
pub static l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value_aux_4) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__6_value) as *mut LeanObject,17804640220912938072 as *mut LeanObject] };
static mut l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7_value) as *mut LeanObject;
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(
    mut v_P_1827_: *mut LeanObject,
    mut v_acc_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1838_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_P_1827_);
                v___x_1829_ = l_Lean_Elab_Tactic_Do_ProofMode_parseHyp_x3f(v_P_1827_);
                if lean_obj_tag(v___x_1829_) == 1 {
                    lean_dec_ref(v_P_1827_);
                    v_val_1830_ = lean_ctor_get(v___x_1829_, 0);
                    lean_inc(v_val_1830_);
                    lean_dec_ref_known(v___x_1829_, 1);
                    v___x_1831_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1831_, 0, v_val_1830_);
                    lean_ctor_set(v___x_1831_, 1, v_acc_1828_);
                    return v___x_1831_;
                } else {
                    lean_dec(v___x_1829_);
                    v___x_1832_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_P_1827_);
                    lean_dec_ref(v_P_1827_);
                    if lean_obj_tag(v___x_1832_) == 1 {
                        v_val_1833_ = lean_ctor_get(v___x_1832_, 0);
                        lean_inc(v_val_1833_);
                        lean_dec_ref_known(v___x_1832_, 1);
                        v_snd_1834_ = lean_ctor_get(v_val_1833_, 1);
                        lean_inc(v_snd_1834_);
                        lean_dec(v_val_1833_);
                        v_snd_1835_ = lean_ctor_get(v_snd_1834_, 1);
                        lean_inc(v_snd_1835_);
                        lean_dec(v_snd_1834_);
                        v_fst_1836_ = lean_ctor_get(v_snd_1835_, 0);
                        lean_inc(v_fst_1836_);
                        v_snd_1837_ = lean_ctor_get(v_snd_1835_, 1);
                        lean_inc(v_snd_1837_);
                        lean_dec(v_snd_1835_);
                        v___x_1838_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(v_snd_1837_, v_acc_1828_);
                        v_P_1827_ = v_fst_1836_;
                        v_acc_1828_ = v___x_1838_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v___x_1832_);
                        return v_acc_1828_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(
    mut v___y_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_1844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_1845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1848_: u8 = 0;
    let mut v___x_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1860_: u8 = 0;
    let mut v_r_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1872_: u8 = 0;
    let mut v_unused_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1842_ = lean_st_ref_get(v___y_1840_);
                v_ngen_1843_ = lean_ctor_get(v___x_1842_, 2);
                lean_inc_ref(v_ngen_1843_);
                lean_dec(v___x_1842_);
                v_namePrefix_1844_ = lean_ctor_get(v_ngen_1843_, 0);
                v_idx_1845_ = lean_ctor_get(v_ngen_1843_, 1);
                v_isSharedCheck_1874_ = (!lean_is_exclusive(v_ngen_1843_)) as u8;
                if v_isSharedCheck_1874_ == 0 {
                    v___x_1847_ = v_ngen_1843_;
                    v_isShared_1848_ = v_isSharedCheck_1874_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_1845_);
                    lean_inc(v_namePrefix_1844_);
                    lean_dec(v_ngen_1843_);
                    v___x_1847_ = lean_box(0);
                    v_isShared_1848_ = v_isSharedCheck_1874_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1849_ = lean_st_ref_take(v___y_1840_);
                v_env_1850_ = lean_ctor_get(v___x_1849_, 0);
                v_nextMacroScope_1851_ = lean_ctor_get(v___x_1849_, 1);
                v_auxDeclNGen_1852_ = lean_ctor_get(v___x_1849_, 3);
                v_traceState_1853_ = lean_ctor_get(v___x_1849_, 4);
                v_cache_1854_ = lean_ctor_get(v___x_1849_, 5);
                v_messages_1855_ = lean_ctor_get(v___x_1849_, 6);
                v_infoState_1856_ = lean_ctor_get(v___x_1849_, 7);
                v_snapshotTasks_1857_ = lean_ctor_get(v___x_1849_, 8);
                v_isSharedCheck_1872_ = (!lean_is_exclusive(v___x_1849_)) as u8;
                if v_isSharedCheck_1872_ == 0 {
                    v_unused_1873_ = lean_ctor_get(v___x_1849_, 2);
                    lean_dec(v_unused_1873_);
                    v___x_1859_ = v___x_1849_;
                    v_isShared_1860_ = v_isSharedCheck_1872_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_1857_);
                    lean_inc(v_infoState_1856_);
                    lean_inc(v_messages_1855_);
                    lean_inc(v_cache_1854_);
                    lean_inc(v_traceState_1853_);
                    lean_inc(v_auxDeclNGen_1852_);
                    lean_inc(v_nextMacroScope_1851_);
                    lean_inc(v_env_1850_);
                    lean_dec(v___x_1849_);
                    v___x_1859_ = lean_box(0);
                    v_isShared_1860_ = v_isSharedCheck_1872_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_1845_);
                lean_inc(v_namePrefix_1844_);
                v_r_1861_ = l_Lean_Name_num___override(v_namePrefix_1844_, v_idx_1845_);
                v___x_1862_ = lean_unsigned_to_nat(1);
                v___x_1863_ = lean_nat_add(v_idx_1845_, v___x_1862_);
                lean_dec(v_idx_1845_);
                if v_isShared_1848_ == 0 {
                    lean_ctor_set(v___x_1847_, 1, v___x_1863_);
                    v___x_1865_ = v___x_1847_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1871_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_namePrefix_1844_);
                    lean_ctor_set(v_reuseFailAlloc_1871_, 1, v___x_1863_);
                    v___x_1865_ = v_reuseFailAlloc_1871_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1860_ == 0 {
                    lean_ctor_set(v___x_1859_, 2, v___x_1865_);
                    v___x_1867_ = v___x_1859_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1870_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_env_1850_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_nextMacroScope_1851_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 2, v___x_1865_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 3, v_auxDeclNGen_1852_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 4, v_traceState_1853_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 5, v_cache_1854_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 6, v_messages_1855_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 7, v_infoState_1856_);
                    lean_ctor_set(v_reuseFailAlloc_1870_, 8, v_snapshotTasks_1857_);
                    v___x_1867_ = v_reuseFailAlloc_1870_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1868_ = lean_st_ref_set(v___y_1840_, v___x_1867_);
                v___x_1869_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1869_, 0, v_r_1861_);
                return v___x_1869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg___boxed(
    mut v___y_1875_: *mut LeanObject,
    mut v___y_1876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1877_: *mut LeanObject = core::ptr::null_mut();
    v_res_1877_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_1875_);
    lean_dec(v___y_1875_);
    return v_res_1877_;
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(
    mut v___y_1878_: *mut LeanObject,
    mut v___y_1879_: *mut LeanObject,
    mut v___y_1880_: *mut LeanObject,
    mut v___y_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_1881_);
    return v___x_1883_;
}
pub unsafe fn l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___boxed(
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1889_: *mut LeanObject = core::ptr::null_mut();
    v_res_1889_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0(v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
    lean_dec(v___y_1887_);
    lean_dec_ref(v___y_1886_);
    lean_dec(v___y_1885_);
    lean_dec_ref(v___y_1884_);
    return v_res_1889_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(
    mut v_msg_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
    mut v___y_1895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3140__overap_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    v___f_1897_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___closed__0;
    v___x_3140__overap_1898_ = lean_panic_fn_borrowed(v___f_1897_, v_msg_1891_);
    lean_inc(v___y_1895_);
    lean_inc_ref(v___y_1894_);
    lean_inc(v___y_1893_);
    lean_inc_ref(v___y_1892_);
    v___x_1899_ = lean_apply_5(
        v___x_3140__overap_1898_,
        v___y_1892_,
        v___y_1893_,
        v___y_1894_,
        v___y_1895_,
        lean_box(0),
    );
    return v___x_1899_;
}
pub unsafe fn l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2___boxed(
    mut v_msg_1900_: *mut LeanObject,
    mut v___y_1901_: *mut LeanObject,
    mut v___y_1902_: *mut LeanObject,
    mut v___y_1903_: *mut LeanObject,
    mut v___y_1904_: *mut LeanObject,
    mut v___y_1905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1906_: *mut LeanObject = core::ptr::null_mut();
    v_res_1906_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v_msg_1900_, v___y_1901_, v___y_1902_, v___y_1903_, v___y_1904_);
    lean_dec(v___y_1904_);
    lean_dec_ref(v___y_1903_);
    lean_dec(v___y_1902_);
    lean_dec_ref(v___y_1901_);
    return v_res_1906_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(
    mut v_a_1910_: *mut LeanObject,
    mut v_Ps_1911_: *mut LeanObject,
    mut v_a_1912_: *mut LeanObject,
    mut v___y_1913_: *mut LeanObject,
    mut v___y_1914_: *mut LeanObject,
    mut v___y_1915_: *mut LeanObject,
    mut v___y_1916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1925_: u8 = 0;
    let mut v_head_1926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v_name_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uniq_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1936_: u8 = 0;
    let mut v___x_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1941_: u8 = 0;
    let mut v___x_1942_: u8 = 0;
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1962_: u8 = 0;
    let mut v_a_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1966_: u8 = 0;
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1970_: u8 = 0;
    let mut v_isSharedCheck_1971_: u8 = 0;
    let mut v_isSharedCheck_1972_: u8 = 0;
    let mut v_a_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1976_: u8 = 0;
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1987_: u8 = 0;
    let mut v_isSharedCheck_1988_: u8 = 0;
    let mut v_unused_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1993_: u8 = 0;
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1997_: u8 = 0;
    let mut v_a_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2001_: u8 = 0;
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2005_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1918_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1;
                v___x_1919_ = l_Lean_Core_mkFreshUserName(v___x_1918_, v___y_1915_, v___y_1916_);
                if lean_obj_tag(v___x_1919_) == 0 {
                    v_a_1920_ = lean_ctor_get(v___x_1919_, 0);
                    lean_inc(v_a_1920_);
                    lean_dec_ref_known(v___x_1919_, 1);
                    v___x_1921_ = l_Lean_mkFreshId___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__0___redArg(v___y_1916_);
                    if lean_obj_tag(v___x_1921_) == 0 {
                        v_snd_1922_ = lean_ctor_get(v_a_1912_, 1);
                        v_isSharedCheck_1988_ = (!lean_is_exclusive(v_a_1912_)) as u8;
                        if v_isSharedCheck_1988_ == 0 {
                            v_unused_1989_ = lean_ctor_get(v_a_1912_, 0);
                            lean_dec(v_unused_1989_);
                            v___x_1924_ = v_a_1912_;
                            v_isShared_1925_ = v_isSharedCheck_1988_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_snd_1922_);
                            lean_dec(v_a_1912_);
                            v___x_1924_ = lean_box(0);
                            v_isShared_1925_ = v_isSharedCheck_1988_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1920_);
                        lean_dec_ref(v_a_1912_);
                        lean_dec(v_Ps_1911_);
                        lean_dec_ref(v_a_1910_);
                        v_a_1990_ = lean_ctor_get(v___x_1921_, 0);
                        v_isSharedCheck_1997_ = (!lean_is_exclusive(v___x_1921_)) as u8;
                        if v_isSharedCheck_1997_ == 0 {
                            v___x_1992_ = v___x_1921_;
                            v_isShared_1993_ = v_isSharedCheck_1997_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_1990_);
                            lean_dec(v___x_1921_);
                            v___x_1992_ = lean_box(0);
                            v_isShared_1993_ = v_isSharedCheck_1997_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_a_1912_);
                    lean_dec(v_Ps_1911_);
                    lean_dec_ref(v_a_1910_);
                    v_a_1998_ = lean_ctor_get(v___x_1919_, 0);
                    v_isSharedCheck_2005_ = (!lean_is_exclusive(v___x_1919_)) as u8;
                    if v_isSharedCheck_2005_ == 0 {
                        v___x_2000_ = v___x_1919_;
                        v_isShared_2001_ = v_isSharedCheck_2005_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_1998_);
                        lean_dec(v___x_1919_);
                        v___x_2000_ = lean_box(0);
                        v_isShared_2001_ = v_isSharedCheck_2005_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_snd_1922_) == 1 {
                    lean_dec_ref_known(v___x_1921_, 1);
                    lean_dec(v_a_1920_);
                    v_head_1926_ = lean_ctor_get(v_snd_1922_, 0);
                    v_tail_1927_ = lean_ctor_get(v_snd_1922_, 1);
                    v_isSharedCheck_1972_ = (!lean_is_exclusive(v_snd_1922_)) as u8;
                    if v_isSharedCheck_1972_ == 0 {
                        v___x_1929_ = v_snd_1922_;
                        v_isShared_1930_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_tail_1927_);
                        lean_inc(v_head_1926_);
                        lean_dec(v_snd_1922_);
                        v___x_1929_ = lean_box(0);
                        v_isShared_1930_ = v_isSharedCheck_1972_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_1973_ = lean_ctor_get(v___x_1921_, 0);
                    v_isSharedCheck_1987_ = (!lean_is_exclusive(v___x_1921_)) as u8;
                    if v_isSharedCheck_1987_ == 0 {
                        v___x_1975_ = v___x_1921_;
                        v_isShared_1976_ = v_isSharedCheck_1987_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1973_);
                        lean_dec(v___x_1921_);
                        v___x_1975_ = lean_box(0);
                        v_isShared_1976_ = v_isSharedCheck_1987_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v_name_1931_ = lean_ctor_get(v_head_1926_, 0);
                v_uniq_1932_ = lean_ctor_get(v_head_1926_, 1);
                v_p_1933_ = lean_ctor_get(v_head_1926_, 2);
                v_isSharedCheck_1971_ = (!lean_is_exclusive(v_head_1926_)) as u8;
                if v_isSharedCheck_1971_ == 0 {
                    v___x_1935_ = v_head_1926_;
                    v_isShared_1936_ = v_isSharedCheck_1971_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_p_1933_);
                    lean_inc(v_uniq_1932_);
                    lean_inc(v_name_1931_);
                    lean_dec(v_head_1926_);
                    v___x_1935_ = lean_box(0);
                    v_isShared_1936_ = v_isSharedCheck_1971_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_inc_ref(v_a_1910_);
                v___x_1937_ = l_Lean_Meta_isExprDefEq(
                    v_p_1933_,
                    v_a_1910_,
                    v___y_1913_,
                    v___y_1914_,
                    v___y_1915_,
                    v___y_1916_,
                );
                if lean_obj_tag(v___x_1937_) == 0 {
                    v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
                    v_isSharedCheck_1962_ = (!lean_is_exclusive(v___x_1937_)) as u8;
                    if v_isSharedCheck_1962_ == 0 {
                        v___x_1940_ = v___x_1937_;
                        v_isShared_1941_ = v_isSharedCheck_1962_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_1938_);
                        lean_dec(v___x_1937_);
                        v___x_1940_ = lean_box(0);
                        v_isShared_1941_ = v_isSharedCheck_1962_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1935_);
                    lean_dec(v_uniq_1932_);
                    lean_dec(v_name_1931_);
                    lean_del_object(v___x_1929_);
                    lean_dec(v_tail_1927_);
                    lean_del_object(v___x_1924_);
                    lean_dec(v_Ps_1911_);
                    lean_dec_ref(v_a_1910_);
                    v_a_1963_ = lean_ctor_get(v___x_1937_, 0);
                    v_isSharedCheck_1970_ = (!lean_is_exclusive(v___x_1937_)) as u8;
                    if v_isSharedCheck_1970_ == 0 {
                        v___x_1965_ = v___x_1937_;
                        v_isShared_1966_ = v_isSharedCheck_1970_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_1963_);
                        lean_dec(v___x_1937_);
                        v___x_1965_ = lean_box(0);
                        v_isShared_1966_ = v_isSharedCheck_1970_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1942_ = (lean_unbox(v_a_1938_) as u8);
                lean_dec(v_a_1938_);
                if v___x_1942_ == 0 {
                    lean_del_object(v___x_1940_);
                    lean_del_object(v___x_1935_);
                    lean_dec(v_uniq_1932_);
                    lean_dec(v_name_1931_);
                    lean_del_object(v___x_1929_);
                    v___x_1943_ = lean_box(0);
                    if v_isShared_1925_ == 0 {
                        lean_ctor_set(v___x_1924_, 1, v_tail_1927_);
                        lean_ctor_set(v___x_1924_, 0, v___x_1943_);
                        v___x_1945_ = v___x_1924_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1947_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1947_, 0, v___x_1943_);
                        lean_ctor_set(v_reuseFailAlloc_1947_, 1, v_tail_1927_);
                        v___x_1945_ = v_reuseFailAlloc_1947_;
                        state = 5;
                        continue;
                    }
                } else {
                    if v_isShared_1936_ == 0 {
                        lean_ctor_set(v___x_1935_, 2, v_a_1910_);
                        v___x_1949_ = v___x_1935_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_name_1931_);
                        lean_ctor_set(v_reuseFailAlloc_1961_, 1, v_uniq_1932_);
                        lean_ctor_set(v_reuseFailAlloc_1961_, 2, v_a_1910_);
                        v___x_1949_ = v_reuseFailAlloc_1961_;
                        state = 6;
                        continue;
                    }
                }
            }
            5 => {
                v_a_1912_ = v___x_1945_;
                state = 0;
                continue;
            }
            6 => {
                v___x_1950_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1949_);
                if v_isShared_1925_ == 0 {
                    lean_ctor_set(v___x_1924_, 1, v___x_1950_);
                    lean_ctor_set(v___x_1924_, 0, v_Ps_1911_);
                    v___x_1952_ = v___x_1924_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_Ps_1911_);
                    lean_ctor_set(v_reuseFailAlloc_1960_, 1, v___x_1950_);
                    v___x_1952_ = v_reuseFailAlloc_1960_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_1953_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1953_, 0, v___x_1952_);
                if v_isShared_1930_ == 0 {
                    lean_ctor_set_tag(v___x_1929_, 0);
                    lean_ctor_set(v___x_1929_, 0, v___x_1953_);
                    v___x_1955_ = v___x_1929_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1959_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1959_, 0, v___x_1953_);
                    lean_ctor_set(v_reuseFailAlloc_1959_, 1, v_tail_1927_);
                    v___x_1955_ = v_reuseFailAlloc_1959_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_1941_ == 0 {
                    lean_ctor_set(v___x_1940_, 0, v___x_1955_);
                    v___x_1957_ = v___x_1940_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1958_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1958_, 0, v___x_1955_);
                    v___x_1957_ = v_reuseFailAlloc_1958_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1957_;
            }
            10 => {
                if v_isShared_1966_ == 0 {
                    v___x_1968_ = v___x_1965_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
                    v___x_1968_ = v_reuseFailAlloc_1969_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1968_;
            }
            12 => {
                v___x_1977_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_1977_, 0, v_a_1920_);
                lean_ctor_set(v___x_1977_, 1, v_a_1973_);
                lean_ctor_set(v___x_1977_, 2, v_a_1910_);
                v___x_1978_ = l_Lean_Elab_Tactic_Do_ProofMode_Hyp_toExpr(v___x_1977_);
                if v_isShared_1925_ == 0 {
                    lean_ctor_set(v___x_1924_, 1, v___x_1978_);
                    lean_ctor_set(v___x_1924_, 0, v_Ps_1911_);
                    v___x_1980_ = v___x_1924_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1986_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_Ps_1911_);
                    lean_ctor_set(v_reuseFailAlloc_1986_, 1, v___x_1978_);
                    v___x_1980_ = v_reuseFailAlloc_1986_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_1981_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1981_, 0, v___x_1980_);
                v___x_1982_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1982_, 0, v___x_1981_);
                lean_ctor_set(v___x_1982_, 1, v_snd_1922_);
                if v_isShared_1976_ == 0 {
                    lean_ctor_set(v___x_1975_, 0, v___x_1982_);
                    v___x_1984_ = v___x_1975_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1985_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1985_, 0, v___x_1982_);
                    v___x_1984_ = v_reuseFailAlloc_1985_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_1984_;
            }
            15 => {
                if v_isShared_1993_ == 0 {
                    v___x_1995_ = v___x_1992_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1996_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1996_, 0, v_a_1990_);
                    v___x_1995_ = v_reuseFailAlloc_1996_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_1995_;
            }
            17 => {
                if v_isShared_2001_ == 0 {
                    v___x_2003_ = v___x_2000_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2004_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_a_1998_);
                    v___x_2003_ = v_reuseFailAlloc_2004_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2003_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___boxed(
    mut v_a_2006_: *mut LeanObject,
    mut v_Ps_2007_: *mut LeanObject,
    mut v_a_2008_: *mut LeanObject,
    mut v___y_2009_: *mut LeanObject,
    mut v___y_2010_: *mut LeanObject,
    mut v___y_2011_: *mut LeanObject,
    mut v___y_2012_: *mut LeanObject,
    mut v___y_2013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2014_: *mut LeanObject = core::ptr::null_mut();
    v_res_2014_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_2006_, v_Ps_2007_, v_a_2008_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
    lean_dec(v___y_2012_);
    lean_dec_ref(v___y_2011_);
    lean_dec(v___y_2010_);
    lean_dec_ref(v___y_2009_);
    return v_res_2014_;
}
pub unsafe fn _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3()
-> *mut LeanObject {
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    v___x_2018_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__2;
    v___x_2019_ = lean_unsigned_to_nat(8);
    v___x_2020_ = lean_unsigned_to_nat(51);
    v___x_2021_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__1;
    v___x_2022_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__0;
    v___x_2023_ = l_mkPanicMessageWithDecl(
        v___x_2022_,
        v___x_2021_,
        v___x_2020_,
        v___x_2019_,
        v___x_2018_,
    );
    return v___x_2023_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(
    mut v_Ps_2024_: *mut LeanObject,
    mut v_P_x27_2025_: *mut LeanObject,
    mut v_a_2026_: *mut LeanObject,
    mut v_a_2027_: *mut LeanObject,
    mut v_a_2028_: *mut LeanObject,
    mut v_a_2029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2035_: u8 = 0;
    let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2057_: u8 = 0;
    let mut v_fst_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2070_: u8 = 0;
    let mut v_isSharedCheck_2071_: u8 = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2078_: u8 = 0;
    let mut v_fst_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2086_: u8 = 0;
    let mut v_a_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2094_: u8 = 0;
    let mut v_isSharedCheck_2095_: u8 = 0;
    let mut v_a_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2099_: u8 = 0;
    let mut v___x_2101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2103_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2031_ =
                    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_P_x27_2025_, v_a_2027_);
                if lean_obj_tag(v___x_2031_) == 0 {
                    v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
                    v_isSharedCheck_2095_ = (!lean_is_exclusive(v___x_2031_)) as u8;
                    if v_isSharedCheck_2095_ == 0 {
                        v___x_2034_ = v___x_2031_;
                        v_isShared_2035_ = v_isSharedCheck_2095_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2032_);
                        lean_dec(v___x_2031_);
                        v___x_2034_ = lean_box(0);
                        v_isShared_2035_ = v_isSharedCheck_2095_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_Ps_2024_);
                    v_a_2096_ = lean_ctor_get(v___x_2031_, 0);
                    v_isSharedCheck_2103_ = (!lean_is_exclusive(v___x_2031_)) as u8;
                    if v_isSharedCheck_2103_ == 0 {
                        v___x_2098_ = v___x_2031_;
                        v_isShared_2099_ = v_isSharedCheck_2103_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2096_);
                        lean_dec(v___x_2031_);
                        v___x_2098_ = lean_box(0);
                        v_isShared_2099_ = v_isSharedCheck_2103_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_a_2032_);
                v___x_2036_ = l_Lean_Elab_Tactic_Do_ProofMode_parseEmptyHyp_x3f(v_a_2032_);
                if lean_obj_tag(v___x_2036_) == 1 {
                    lean_dec_ref_known(v___x_2036_, 1);
                    v___x_2037_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2037_, 0, v_Ps_2024_);
                    lean_ctor_set(v___x_2037_, 1, v_a_2032_);
                    if v_isShared_2035_ == 0 {
                        lean_ctor_set(v___x_2034_, 0, v___x_2037_);
                        v___x_2039_ = v___x_2034_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
                        v___x_2039_ = v_reuseFailAlloc_2040_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2036_);
                    lean_del_object(v___x_2034_);
                    v___x_2041_ = l_Lean_Elab_Tactic_Do_ProofMode_parseAnd_x3f(v_a_2032_);
                    if lean_obj_tag(v___x_2041_) == 1 {
                        lean_dec(v_a_2032_);
                        v_val_2042_ = lean_ctor_get(v___x_2041_, 0);
                        lean_inc(v_val_2042_);
                        lean_dec_ref_known(v___x_2041_, 1);
                        v_snd_2043_ = lean_ctor_get(v_val_2042_, 1);
                        lean_inc(v_snd_2043_);
                        v_snd_2044_ = lean_ctor_get(v_snd_2043_, 1);
                        lean_inc(v_snd_2044_);
                        v_fst_2045_ = lean_ctor_get(v_val_2042_, 0);
                        lean_inc(v_fst_2045_);
                        lean_dec(v_val_2042_);
                        v_fst_2046_ = lean_ctor_get(v_snd_2043_, 0);
                        lean_inc(v_fst_2046_);
                        lean_dec(v_snd_2043_);
                        v_fst_2047_ = lean_ctor_get(v_snd_2044_, 0);
                        lean_inc(v_fst_2047_);
                        v_snd_2048_ = lean_ctor_get(v_snd_2044_, 1);
                        lean_inc(v_snd_2048_);
                        lean_dec(v_snd_2044_);
                        v___x_2049_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_2024_, v_fst_2047_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
                        if lean_obj_tag(v___x_2049_) == 0 {
                            v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
                            lean_inc(v_a_2050_);
                            lean_dec_ref_known(v___x_2049_, 1);
                            v_fst_2051_ = lean_ctor_get(v_a_2050_, 0);
                            lean_inc(v_fst_2051_);
                            v_snd_2052_ = lean_ctor_get(v_a_2050_, 1);
                            lean_inc(v_snd_2052_);
                            lean_dec(v_a_2050_);
                            v___x_2053_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_fst_2051_, v_snd_2048_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
                            if lean_obj_tag(v___x_2053_) == 0 {
                                v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
                                v_isSharedCheck_2071_ = (!lean_is_exclusive(v___x_2053_)) as u8;
                                if v_isSharedCheck_2071_ == 0 {
                                    v___x_2056_ = v___x_2053_;
                                    v_isShared_2057_ = v_isSharedCheck_2071_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_2054_);
                                    lean_dec(v___x_2053_);
                                    v___x_2056_ = lean_box(0);
                                    v_isShared_2057_ = v_isSharedCheck_2071_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                lean_dec(v_snd_2052_);
                                lean_dec(v_fst_2046_);
                                lean_dec(v_fst_2045_);
                                return v___x_2053_;
                            }
                        } else {
                            lean_dec(v_snd_2048_);
                            lean_dec(v_fst_2046_);
                            lean_dec(v_fst_2045_);
                            return v___x_2049_;
                        }
                    } else {
                        lean_dec(v___x_2041_);
                        v___x_2072_ = lean_box(0);
                        lean_inc(v_Ps_2024_);
                        v___x_2073_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2073_, 0, v___x_2072_);
                        lean_ctor_set(v___x_2073_, 1, v_Ps_2024_);
                        v___x_2074_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_2032_, v_Ps_2024_, v___x_2073_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
                        if lean_obj_tag(v___x_2074_) == 0 {
                            v_a_2075_ = lean_ctor_get(v___x_2074_, 0);
                            v_isSharedCheck_2086_ = (!lean_is_exclusive(v___x_2074_)) as u8;
                            if v_isSharedCheck_2086_ == 0 {
                                v___x_2077_ = v___x_2074_;
                                v_isShared_2078_ = v_isSharedCheck_2086_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2075_);
                                lean_dec(v___x_2074_);
                                v___x_2077_ = lean_box(0);
                                v_isShared_2078_ = v_isSharedCheck_2086_;
                                state = 7;
                                continue;
                            }
                        } else {
                            v_a_2087_ = lean_ctor_get(v___x_2074_, 0);
                            v_isSharedCheck_2094_ = (!lean_is_exclusive(v___x_2074_)) as u8;
                            if v_isSharedCheck_2094_ == 0 {
                                v___x_2089_ = v___x_2074_;
                                v_isShared_2090_ = v_isSharedCheck_2094_;
                                state = 9;
                                continue;
                            } else {
                                lean_inc(v_a_2087_);
                                lean_dec(v___x_2074_);
                                v___x_2089_ = lean_box(0);
                                v_isShared_2090_ = v_isSharedCheck_2094_;
                                state = 9;
                                continue;
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_2039_;
            }
            3 => {
                v_fst_2058_ = lean_ctor_get(v_a_2054_, 0);
                v_snd_2059_ = lean_ctor_get(v_a_2054_, 1);
                v_isSharedCheck_2070_ = (!lean_is_exclusive(v_a_2054_)) as u8;
                if v_isSharedCheck_2070_ == 0 {
                    v___x_2061_ = v_a_2054_;
                    v_isShared_2062_ = v_isSharedCheck_2070_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_2059_);
                    lean_inc(v_fst_2058_);
                    lean_dec(v_a_2054_);
                    v___x_2061_ = lean_box(0);
                    v_isShared_2062_ = v_isSharedCheck_2070_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2063_ = l_Lean_Elab_Tactic_Do_ProofMode_SPred_mkAnd_x21(
                    v_fst_2045_,
                    v_fst_2046_,
                    v_snd_2052_,
                    v_snd_2059_,
                );
                if v_isShared_2062_ == 0 {
                    lean_ctor_set(v___x_2061_, 1, v___x_2063_);
                    v___x_2065_ = v___x_2061_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2069_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_fst_2058_);
                    lean_ctor_set(v_reuseFailAlloc_2069_, 1, v___x_2063_);
                    v___x_2065_ = v_reuseFailAlloc_2069_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2057_ == 0 {
                    lean_ctor_set(v___x_2056_, 0, v___x_2065_);
                    v___x_2067_ = v___x_2056_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2068_, 0, v___x_2065_);
                    v___x_2067_ = v_reuseFailAlloc_2068_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2067_;
            }
            7 => {
                v_fst_2079_ = lean_ctor_get(v_a_2075_, 0);
                lean_inc(v_fst_2079_);
                lean_dec(v_a_2075_);
                if lean_obj_tag(v_fst_2079_) == 0 {
                    lean_del_object(v___x_2077_);
                    v___x_2080_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3_once), _init_l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___closed__3);
                    v___x_2081_ = l_panic___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__2(v___x_2080_, v_a_2026_, v_a_2027_, v_a_2028_, v_a_2029_);
                    return v___x_2081_;
                } else {
                    v_val_2082_ = lean_ctor_get(v_fst_2079_, 0);
                    lean_inc(v_val_2082_);
                    lean_dec_ref_known(v_fst_2079_, 1);
                    if v_isShared_2078_ == 0 {
                        lean_ctor_set(v___x_2077_, 0, v_val_2082_);
                        v___x_2084_ = v___x_2077_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_val_2082_);
                        v___x_2084_ = v_reuseFailAlloc_2085_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                return v___x_2084_;
            }
            9 => {
                if v_isShared_2090_ == 0 {
                    v___x_2092_ = v___x_2089_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
                    v___x_2092_ = v_reuseFailAlloc_2093_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2092_;
            }
            11 => {
                if v_isShared_2099_ == 0 {
                    v___x_2101_ = v___x_2098_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2102_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2102_, 0, v_a_2096_);
                    v___x_2101_ = v_reuseFailAlloc_2102_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2101_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label___boxed(
    mut v_Ps_2104_: *mut LeanObject,
    mut v_P_x27_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2111_: *mut LeanObject = core::ptr::null_mut();
    v_res_2111_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v_Ps_2104_, v_P_x27_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_);
    lean_dec(v_a_2109_);
    lean_dec_ref(v_a_2108_);
    lean_dec(v_a_2107_);
    lean_dec_ref(v_a_2106_);
    return v_res_2111_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(
    mut v_a_2112_: *mut LeanObject,
    mut v_Ps_2113_: *mut LeanObject,
    mut v_inst_2114_: *mut LeanObject,
    mut v_a_2115_: *mut LeanObject,
    mut v___y_2116_: *mut LeanObject,
    mut v___y_2117_: *mut LeanObject,
    mut v___y_2118_: *mut LeanObject,
    mut v___y_2119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    v___x_2121_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg(v_a_2112_, v_Ps_2113_, v_a_2115_, v___y_2116_, v___y_2117_, v___y_2118_, v___y_2119_);
    return v___x_2121_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___boxed(
    mut v_a_2122_: *mut LeanObject,
    mut v_Ps_2123_: *mut LeanObject,
    mut v_inst_2124_: *mut LeanObject,
    mut v_a_2125_: *mut LeanObject,
    mut v___y_2126_: *mut LeanObject,
    mut v___y_2127_: *mut LeanObject,
    mut v___y_2128_: *mut LeanObject,
    mut v___y_2129_: *mut LeanObject,
    mut v___y_2130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2131_: *mut LeanObject = core::ptr::null_mut();
    v_res_2131_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1(v_a_2122_, v_Ps_2123_, v_inst_2124_, v_a_2125_, v___y_2126_, v___y_2127_, v___y_2128_, v___y_2129_);
    lean_dec(v___y_2129_);
    lean_dec_ref(v___y_2128_);
    lean_dec(v___y_2127_);
    lean_dec_ref(v___y_2126_);
    return v_res_2131_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(
    mut v_P_2132_: *mut LeanObject,
    mut v_P_x27_2133_: *mut LeanObject,
    mut v_a_2134_: *mut LeanObject,
    mut v_a_2135_: *mut LeanObject,
    mut v_a_2136_: *mut LeanObject,
    mut v_a_2137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2145_: u8 = 0;
    let mut v_snd_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_a_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2154_: u8 = 0;
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2139_ = lean_box(0);
                v___x_2140_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_collectHyps(v_P_2132_, v___x_2139_);
                v___x_2141_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label(v___x_2140_, v_P_x27_2133_, v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
                if lean_obj_tag(v___x_2141_) == 0 {
                    v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
                    v_isSharedCheck_2150_ = (!lean_is_exclusive(v___x_2141_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v___x_2144_ = v___x_2141_;
                        v_isShared_2145_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2142_);
                        lean_dec(v___x_2141_);
                        v___x_2144_ = lean_box(0);
                        v_isShared_2145_ = v_isSharedCheck_2150_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2151_ = lean_ctor_get(v___x_2141_, 0);
                    v_isSharedCheck_2158_ = (!lean_is_exclusive(v___x_2141_)) as u8;
                    if v_isSharedCheck_2158_ == 0 {
                        v___x_2153_ = v___x_2141_;
                        v_isShared_2154_ = v_isSharedCheck_2158_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2151_);
                        lean_dec(v___x_2141_);
                        v___x_2153_ = lean_box(0);
                        v_isShared_2154_ = v_isSharedCheck_2158_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2146_ = lean_ctor_get(v_a_2142_, 1);
                lean_inc(v_snd_2146_);
                lean_dec(v_a_2142_);
                if v_isShared_2145_ == 0 {
                    lean_ctor_set(v___x_2144_, 0, v_snd_2146_);
                    v___x_2148_ = v___x_2144_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_snd_2146_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2148_;
            }
            3 => {
                if v_isShared_2154_ == 0 {
                    v___x_2156_ = v___x_2153_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
                    v___x_2156_ = v_reuseFailAlloc_2157_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2156_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed(
    mut v_P_2159_: *mut LeanObject,
    mut v_P_x27_2160_: *mut LeanObject,
    mut v_a_2161_: *mut LeanObject,
    mut v_a_2162_: *mut LeanObject,
    mut v_a_2163_: *mut LeanObject,
    mut v_a_2164_: *mut LeanObject,
    mut v_a_2165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2166_: *mut LeanObject = core::ptr::null_mut();
    v_res_2166_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(
        v_P_2159_,
        v_P_x27_2160_,
        v_a_2161_,
        v_a_2162_,
        v_a_2163_,
        v_a_2164_,
    );
    lean_dec(v_a_2164_);
    lean_dec_ref(v_a_2163_);
    lean_dec(v_a_2162_);
    lean_dec_ref(v_a_2161_);
    return v_res_2166_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0(
    mut v_toApplicative_2169_: *mut LeanObject,
    mut v___x_2170_: *mut LeanObject,
    mut v___x_2171_: *mut LeanObject,
    mut v___x_2172_: *mut LeanObject,
    mut v___x_2173_: *mut LeanObject,
    mut v___x_2174_: *mut LeanObject,
    mut v_00_u03c3s_2175_: *mut LeanObject,
    mut v_hyps_2176_: *mut LeanObject,
    mut v_P_x27_2177_: *mut LeanObject,
    mut v_target_2178_: *mut LeanObject,
    mut v_00_u03c6_2179_: *mut LeanObject,
    mut v_a_2180_: *mut LeanObject,
    mut v_prf_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toPure_2182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prf_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    v_toPure_2182_ = lean_ctor_get(v_toApplicative_2169_, 1);
    lean_inc(v_toPure_2182_);
    lean_dec_ref(v_toApplicative_2169_);
    v___x_2183_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0;
    v___x_2184_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1;
    v___x_2185_ = l_Lean_Name_mkStr6(
        v___x_2170_,
        v___x_2171_,
        v___x_2172_,
        v___x_2173_,
        v___x_2183_,
        v___x_2184_,
    );
    v___x_2186_ = l_Lean_mkConst(v___x_2185_, v___x_2174_);
    v_prf_2187_ = l_Lean_mkApp7(
        v___x_2186_,
        v_00_u03c3s_2175_,
        v_hyps_2176_,
        v_P_x27_2177_,
        v_target_2178_,
        v_00_u03c6_2179_,
        v_a_2180_,
        v_prf_2181_,
    );
    v___x_2188_ = lean_apply_2(v_toPure_2182_, lean_box(0), v_prf_2187_);
    return v___x_2188_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(
    mut v_h_u03c6_2189_: *mut LeanObject,
    mut v_____do__lift_2190_: u8,
    mut v___x_2191_: u8,
    mut v_inst_2192_: *mut LeanObject,
    mut v_toBind_2193_: *mut LeanObject,
    mut v___f_2194_: *mut LeanObject,
    mut v_prf_2195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: u8 = 0;
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    v___x_2196_ = lean_unsigned_to_nat(1);
    v___x_2197_ = lean_mk_empty_array_with_capacity(v___x_2196_);
    v___x_2198_ = lean_array_push(v___x_2197_, v_h_u03c6_2189_);
    v___x_2199_ = 1;
    v___x_2200_ = lean_box((v_____do__lift_2190_) as usize);
    v___x_2201_ = lean_box((v___x_2191_) as usize);
    v___x_2202_ = lean_box((v_____do__lift_2190_) as usize);
    v___x_2203_ = lean_box((v___x_2191_) as usize);
    v___x_2204_ = lean_box((v___x_2199_) as usize);
    v___x_2205_ = lean_alloc_closure(
        l_Lean_Meta_mkLambdaFVars___boxed as *mut core::ffi::c_void,
        12,
        7,
    );
    lean_closure_set(v___x_2205_, 0, v___x_2198_);
    lean_closure_set(v___x_2205_, 1, v_prf_2195_);
    lean_closure_set(v___x_2205_, 2, v___x_2200_);
    lean_closure_set(v___x_2205_, 3, v___x_2201_);
    lean_closure_set(v___x_2205_, 4, v___x_2202_);
    lean_closure_set(v___x_2205_, 5, v___x_2203_);
    lean_closure_set(v___x_2205_, 6, v___x_2204_);
    v___x_2206_ = lean_apply_2(v_inst_2192_, lean_box(0), v___x_2205_);
    v___x_2207_ = lean_apply_4(
        v_toBind_2193_,
        lean_box(0),
        lean_box(0),
        v___x_2206_,
        v___f_2194_,
    );
    return v___x_2207_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1___boxed(
    mut v_h_u03c6_2208_: *mut LeanObject,
    mut v_____do__lift_2209_: *mut LeanObject,
    mut v___x_2210_: *mut LeanObject,
    mut v_inst_2211_: *mut LeanObject,
    mut v_toBind_2212_: *mut LeanObject,
    mut v___f_2213_: *mut LeanObject,
    mut v_prf_2214_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_503__boxed_2215_: u8 = 0;
    let mut v___x_504__boxed_2216_: u8 = 0;
    let mut v_res_2217_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_503__boxed_2215_ = (lean_unbox(v_____do__lift_2209_) as u8);
    v___x_504__boxed_2216_ = (lean_unbox(v___x_2210_) as u8);
    v_res_2217_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1(
        v_h_u03c6_2208_,
        v_____do__lift_503__boxed_2215_,
        v___x_504__boxed_2216_,
        v_inst_2211_,
        v_toBind_2212_,
        v___f_2213_,
        v_prf_2214_,
    );
    return v_res_2217_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(
    mut v_____do__lift_2218_: u8,
    mut v___x_2219_: u8,
    mut v_inst_2220_: *mut LeanObject,
    mut v_toBind_2221_: *mut LeanObject,
    mut v___f_2222_: *mut LeanObject,
    mut v_kSuccess_2223_: *mut LeanObject,
    mut v_00_u03c6_2224_: *mut LeanObject,
    mut v_goal_2225_: *mut LeanObject,
    mut v_h_u03c6_2226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    v___x_2227_ = lean_box((v_____do__lift_2218_) as usize);
    v___x_2228_ = lean_box((v___x_2219_) as usize);
    lean_inc(v_toBind_2221_);
    lean_inc_ref(v_h_u03c6_2226_);
    v___f_2229_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_2229_, 0, v_h_u03c6_2226_);
    lean_closure_set(v___f_2229_, 1, v___x_2227_);
    lean_closure_set(v___f_2229_, 2, v___x_2228_);
    lean_closure_set(v___f_2229_, 3, v_inst_2220_);
    lean_closure_set(v___f_2229_, 4, v_toBind_2221_);
    lean_closure_set(v___f_2229_, 5, v___f_2222_);
    v___x_2230_ = lean_apply_3(
        v_kSuccess_2223_,
        v_00_u03c6_2224_,
        v_h_u03c6_2226_,
        v_goal_2225_,
    );
    v___x_2231_ = lean_apply_4(
        v_toBind_2221_,
        lean_box(0),
        lean_box(0),
        v___x_2230_,
        v___f_2229_,
    );
    return v___x_2231_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2___boxed(
    mut v_____do__lift_2232_: *mut LeanObject,
    mut v___x_2233_: *mut LeanObject,
    mut v_inst_2234_: *mut LeanObject,
    mut v_toBind_2235_: *mut LeanObject,
    mut v___f_2236_: *mut LeanObject,
    mut v_kSuccess_2237_: *mut LeanObject,
    mut v_00_u03c6_2238_: *mut LeanObject,
    mut v_goal_2239_: *mut LeanObject,
    mut v_h_u03c6_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_539__boxed_2241_: u8 = 0;
    let mut v___x_540__boxed_2242_: u8 = 0;
    let mut v_res_2243_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_539__boxed_2241_ = (lean_unbox(v_____do__lift_2232_) as u8);
    v___x_540__boxed_2242_ = (lean_unbox(v___x_2233_) as u8);
    v_res_2243_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2(
        v_____do__lift_539__boxed_2241_,
        v___x_540__boxed_2242_,
        v_inst_2234_,
        v_toBind_2235_,
        v___f_2236_,
        v_kSuccess_2237_,
        v_00_u03c6_2238_,
        v_goal_2239_,
        v_h_u03c6_2240_,
    );
    return v_res_2243_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3(
    mut v_inst_2244_: *mut LeanObject,
    mut v_inst_2245_: *mut LeanObject,
    mut v_00_u03c6_2246_: *mut LeanObject,
    mut v___f_2247_: *mut LeanObject,
    mut v_____do__lift_2248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    v___x_2249_ = l_Lean_Meta_withLocalDeclD___redArg(
        v_inst_2244_,
        v_inst_2245_,
        v_____do__lift_2248_,
        v_00_u03c6_2246_,
        v___f_2247_,
    );
    return v___x_2249_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(
    mut v___x_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
    mut v___y_2253_: *mut LeanObject,
    mut v___y_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    v___x_2256_ = l_Lean_Core_mkFreshUserName(v___x_2250_, v___y_2253_, v___y_2254_);
    return v___x_2256_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4___boxed(
    mut v___x_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2263_: *mut LeanObject = core::ptr::null_mut();
    v_res_2263_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__4(
        v___x_2257_,
        v___y_2258_,
        v___y_2259_,
        v___y_2260_,
        v___y_2261_,
    );
    lean_dec(v___y_2261_);
    lean_dec_ref(v___y_2260_);
    lean_dec(v___y_2259_);
    lean_dec_ref(v___y_2258_);
    return v_res_2263_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(
    mut v_toApplicative_2266_: *mut LeanObject,
    mut v___x_2267_: *mut LeanObject,
    mut v___x_2268_: *mut LeanObject,
    mut v___x_2269_: *mut LeanObject,
    mut v___x_2270_: *mut LeanObject,
    mut v___x_2271_: *mut LeanObject,
    mut v_00_u03c3s_2272_: *mut LeanObject,
    mut v_hyps_2273_: *mut LeanObject,
    mut v_target_2274_: *mut LeanObject,
    mut v_00_u03c6_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_u_2277_: *mut LeanObject,
    mut v_____do__lift_2278_: u8,
    mut v___x_2279_: u8,
    mut v_inst_2280_: *mut LeanObject,
    mut v_toBind_2281_: *mut LeanObject,
    mut v_kSuccess_2282_: *mut LeanObject,
    mut v_inst_2283_: *mut LeanObject,
    mut v_inst_2284_: *mut LeanObject,
    mut v_P_x27_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_goal_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_00_u03c6_2275_, 2);
    lean_inc_ref(v_target_2274_);
    lean_inc_ref(v_P_x27_2285_);
    lean_inc_ref(v_00_u03c3s_2272_);
    v___f_2286_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0 as *mut core::ffi::c_void,
        13,
        12,
    );
    lean_closure_set(v___f_2286_, 0, v_toApplicative_2266_);
    lean_closure_set(v___f_2286_, 1, v___x_2267_);
    lean_closure_set(v___f_2286_, 2, v___x_2268_);
    lean_closure_set(v___f_2286_, 3, v___x_2269_);
    lean_closure_set(v___f_2286_, 4, v___x_2270_);
    lean_closure_set(v___f_2286_, 5, v___x_2271_);
    lean_closure_set(v___f_2286_, 6, v_00_u03c3s_2272_);
    lean_closure_set(v___f_2286_, 7, v_hyps_2273_);
    lean_closure_set(v___f_2286_, 8, v_P_x27_2285_);
    lean_closure_set(v___f_2286_, 9, v_target_2274_);
    lean_closure_set(v___f_2286_, 10, v_00_u03c6_2275_);
    lean_closure_set(v___f_2286_, 11, v_a_2276_);
    v_goal_2287_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v_goal_2287_, 0, v_u_2277_);
    lean_ctor_set(v_goal_2287_, 1, v_00_u03c3s_2272_);
    lean_ctor_set(v_goal_2287_, 2, v_P_x27_2285_);
    lean_ctor_set(v_goal_2287_, 3, v_target_2274_);
    v___x_2288_ = lean_box((v_____do__lift_2278_) as usize);
    v___x_2289_ = lean_box((v___x_2279_) as usize);
    lean_inc(v_toBind_2281_);
    lean_inc(v_inst_2280_);
    v___f_2290_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_2290_, 0, v___x_2288_);
    lean_closure_set(v___f_2290_, 1, v___x_2289_);
    lean_closure_set(v___f_2290_, 2, v_inst_2280_);
    lean_closure_set(v___f_2290_, 3, v_toBind_2281_);
    lean_closure_set(v___f_2290_, 4, v___f_2286_);
    lean_closure_set(v___f_2290_, 5, v_kSuccess_2282_);
    lean_closure_set(v___f_2290_, 6, v_00_u03c6_2275_);
    lean_closure_set(v___f_2290_, 7, v_goal_2287_);
    v___f_2291_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__3 as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2291_, 0, v_inst_2283_);
    lean_closure_set(v___f_2291_, 1, v_inst_2284_);
    lean_closure_set(v___f_2291_, 2, v_00_u03c6_2275_);
    lean_closure_set(v___f_2291_, 3, v___f_2290_);
    v___f_2292_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___closed__0;
    v___x_2293_ = lean_apply_2(v_inst_2280_, lean_box(0), v___f_2292_);
    v___x_2294_ = lean_apply_4(
        v_toBind_2281_,
        lean_box(0),
        lean_box(0),
        v___x_2293_,
        v___f_2291_,
    );
    return v___x_2294_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2295_: *mut LeanObject = *_args.add(0);
    let mut v___x_2296_: *mut LeanObject = *_args.add(1);
    let mut v___x_2297_: *mut LeanObject = *_args.add(2);
    let mut v___x_2298_: *mut LeanObject = *_args.add(3);
    let mut v___x_2299_: *mut LeanObject = *_args.add(4);
    let mut v___x_2300_: *mut LeanObject = *_args.add(5);
    let mut v_00_u03c3s_2301_: *mut LeanObject = *_args.add(6);
    let mut v_hyps_2302_: *mut LeanObject = *_args.add(7);
    let mut v_target_2303_: *mut LeanObject = *_args.add(8);
    let mut v_00_u03c6_2304_: *mut LeanObject = *_args.add(9);
    let mut v_a_2305_: *mut LeanObject = *_args.add(10);
    let mut v_u_2306_: *mut LeanObject = *_args.add(11);
    let mut v_____do__lift_2307_: *mut LeanObject = *_args.add(12);
    let mut v___x_2308_: *mut LeanObject = *_args.add(13);
    let mut v_inst_2309_: *mut LeanObject = *_args.add(14);
    let mut v_toBind_2310_: *mut LeanObject = *_args.add(15);
    let mut v_kSuccess_2311_: *mut LeanObject = *_args.add(16);
    let mut v_inst_2312_: *mut LeanObject = *_args.add(17);
    let mut v_inst_2313_: *mut LeanObject = *_args.add(18);
    let mut v_P_x27_2314_: *mut LeanObject = *_args.add(19);
    let mut v_____do__lift_604__boxed_2315_: u8 = 0;
    let mut v___x_605__boxed_2316_: u8 = 0;
    let mut v_res_2317_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_604__boxed_2315_ = (lean_unbox(v_____do__lift_2307_) as u8);
    v___x_605__boxed_2316_ = (lean_unbox(v___x_2308_) as u8);
    v_res_2317_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5(
        v_toApplicative_2295_,
        v___x_2296_,
        v___x_2297_,
        v___x_2298_,
        v___x_2299_,
        v___x_2300_,
        v_00_u03c3s_2301_,
        v_hyps_2302_,
        v_target_2303_,
        v_00_u03c6_2304_,
        v_a_2305_,
        v_u_2306_,
        v_____do__lift_604__boxed_2315_,
        v___x_605__boxed_2316_,
        v_inst_2309_,
        v_toBind_2310_,
        v_kSuccess_2311_,
        v_inst_2312_,
        v_inst_2313_,
        v_P_x27_2314_,
    );
    return v_res_2317_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(
    mut v_toApplicative_2318_: *mut LeanObject,
    mut v___x_2319_: *mut LeanObject,
    mut v___x_2320_: *mut LeanObject,
    mut v___x_2321_: *mut LeanObject,
    mut v___x_2322_: *mut LeanObject,
    mut v___x_2323_: *mut LeanObject,
    mut v_00_u03c3s_2324_: *mut LeanObject,
    mut v_hyps_2325_: *mut LeanObject,
    mut v_target_2326_: *mut LeanObject,
    mut v_00_u03c6_2327_: *mut LeanObject,
    mut v_a_2328_: *mut LeanObject,
    mut v_u_2329_: *mut LeanObject,
    mut v_inst_2330_: *mut LeanObject,
    mut v_toBind_2331_: *mut LeanObject,
    mut v_kSuccess_2332_: *mut LeanObject,
    mut v_inst_2333_: *mut LeanObject,
    mut v_inst_2334_: *mut LeanObject,
    mut v_P_x27_2335_: *mut LeanObject,
    mut v_kFail_2336_: *mut LeanObject,
    mut v_____do__lift_2337_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2337_ == 0 {
        let mut v___x_2338_: u8 = 0;
        let mut v___x_2339_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
        v___x_2338_ = 1;
        v___x_2339_ = lean_box((v_____do__lift_2337_) as usize);
        v___x_2340_ = lean_box((v___x_2338_) as usize);
        lean_inc(v_toBind_2331_);
        lean_inc(v_inst_2330_);
        lean_inc_ref(v_hyps_2325_);
        v___f_2341_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__5___boxed
                as *mut core::ffi::c_void,
            20,
            19,
        );
        lean_closure_set(v___f_2341_, 0, v_toApplicative_2318_);
        lean_closure_set(v___f_2341_, 1, v___x_2319_);
        lean_closure_set(v___f_2341_, 2, v___x_2320_);
        lean_closure_set(v___f_2341_, 3, v___x_2321_);
        lean_closure_set(v___f_2341_, 4, v___x_2322_);
        lean_closure_set(v___f_2341_, 5, v___x_2323_);
        lean_closure_set(v___f_2341_, 6, v_00_u03c3s_2324_);
        lean_closure_set(v___f_2341_, 7, v_hyps_2325_);
        lean_closure_set(v___f_2341_, 8, v_target_2326_);
        lean_closure_set(v___f_2341_, 9, v_00_u03c6_2327_);
        lean_closure_set(v___f_2341_, 10, v_a_2328_);
        lean_closure_set(v___f_2341_, 11, v_u_2329_);
        lean_closure_set(v___f_2341_, 12, v___x_2339_);
        lean_closure_set(v___f_2341_, 13, v___x_2340_);
        lean_closure_set(v___f_2341_, 14, v_inst_2330_);
        lean_closure_set(v___f_2341_, 15, v_toBind_2331_);
        lean_closure_set(v___f_2341_, 16, v_kSuccess_2332_);
        lean_closure_set(v___f_2341_, 17, v_inst_2333_);
        lean_closure_set(v___f_2341_, 18, v_inst_2334_);
        v___x_2342_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames___boxed as *mut core::ffi::c_void,
            7,
            2,
        );
        lean_closure_set(v___x_2342_, 0, v_hyps_2325_);
        lean_closure_set(v___x_2342_, 1, v_P_x27_2335_);
        v___x_2343_ = lean_apply_2(v_inst_2330_, lean_box(0), v___x_2342_);
        v___x_2344_ = lean_apply_4(
            v_toBind_2331_,
            lean_box(0),
            lean_box(0),
            v___x_2343_,
            v___f_2341_,
        );
        return v___x_2344_;
    } else {
        lean_dec_ref(v_P_x27_2335_);
        lean_dec_ref(v_inst_2334_);
        lean_dec_ref(v_inst_2333_);
        lean_dec(v_kSuccess_2332_);
        lean_dec(v_toBind_2331_);
        lean_dec(v_inst_2330_);
        lean_dec(v_u_2329_);
        lean_dec_ref(v_a_2328_);
        lean_dec_ref(v_00_u03c6_2327_);
        lean_dec_ref(v_target_2326_);
        lean_dec_ref(v_hyps_2325_);
        lean_dec_ref(v_00_u03c3s_2324_);
        lean_dec(v___x_2323_);
        lean_dec_ref(v___x_2322_);
        lean_dec_ref(v___x_2321_);
        lean_dec_ref(v___x_2320_);
        lean_dec_ref(v___x_2319_);
        lean_dec_ref(v_toApplicative_2318_);
        lean_inc(v_kFail_2336_);
        return v_kFail_2336_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2345_: *mut LeanObject = *_args.add(0);
    let mut v___x_2346_: *mut LeanObject = *_args.add(1);
    let mut v___x_2347_: *mut LeanObject = *_args.add(2);
    let mut v___x_2348_: *mut LeanObject = *_args.add(3);
    let mut v___x_2349_: *mut LeanObject = *_args.add(4);
    let mut v___x_2350_: *mut LeanObject = *_args.add(5);
    let mut v_00_u03c3s_2351_: *mut LeanObject = *_args.add(6);
    let mut v_hyps_2352_: *mut LeanObject = *_args.add(7);
    let mut v_target_2353_: *mut LeanObject = *_args.add(8);
    let mut v_00_u03c6_2354_: *mut LeanObject = *_args.add(9);
    let mut v_a_2355_: *mut LeanObject = *_args.add(10);
    let mut v_u_2356_: *mut LeanObject = *_args.add(11);
    let mut v_inst_2357_: *mut LeanObject = *_args.add(12);
    let mut v_toBind_2358_: *mut LeanObject = *_args.add(13);
    let mut v_kSuccess_2359_: *mut LeanObject = *_args.add(14);
    let mut v_inst_2360_: *mut LeanObject = *_args.add(15);
    let mut v_inst_2361_: *mut LeanObject = *_args.add(16);
    let mut v_P_x27_2362_: *mut LeanObject = *_args.add(17);
    let mut v_kFail_2363_: *mut LeanObject = *_args.add(18);
    let mut v_____do__lift_2364_: *mut LeanObject = *_args.add(19);
    let mut v_____do__lift_658__boxed_2365_: u8 = 0;
    let mut v_res_2366_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_658__boxed_2365_ = (lean_unbox(v_____do__lift_2364_) as u8);
    v_res_2366_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6(
        v_toApplicative_2345_,
        v___x_2346_,
        v___x_2347_,
        v___x_2348_,
        v___x_2349_,
        v___x_2350_,
        v_00_u03c3s_2351_,
        v_hyps_2352_,
        v_target_2353_,
        v_00_u03c6_2354_,
        v_a_2355_,
        v_u_2356_,
        v_inst_2357_,
        v_toBind_2358_,
        v_kSuccess_2359_,
        v_inst_2360_,
        v_inst_2361_,
        v_P_x27_2362_,
        v_kFail_2363_,
        v_____do__lift_658__boxed_2365_,
    );
    lean_dec(v_kFail_2363_);
    return v_res_2366_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(
    mut v_toApplicative_2370_: *mut LeanObject,
    mut v___x_2371_: *mut LeanObject,
    mut v___x_2372_: *mut LeanObject,
    mut v___x_2373_: *mut LeanObject,
    mut v___x_2374_: *mut LeanObject,
    mut v___x_2375_: *mut LeanObject,
    mut v_00_u03c3s_2376_: *mut LeanObject,
    mut v_hyps_2377_: *mut LeanObject,
    mut v_target_2378_: *mut LeanObject,
    mut v_00_u03c6_2379_: *mut LeanObject,
    mut v_u_2380_: *mut LeanObject,
    mut v_inst_2381_: *mut LeanObject,
    mut v_toBind_2382_: *mut LeanObject,
    mut v_kSuccess_2383_: *mut LeanObject,
    mut v_inst_2384_: *mut LeanObject,
    mut v_inst_2385_: *mut LeanObject,
    mut v_P_x27_2386_: *mut LeanObject,
    mut v_kFail_2387_: *mut LeanObject,
    mut v___x_2388_: *mut LeanObject,
    mut v_____do__lift_2389_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2389_) == 1 {
        let mut v_a_2390_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2391_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
        v_a_2390_ = lean_ctor_get(v_____do__lift_2389_, 0);
        lean_inc(v_a_2390_);
        lean_dec_ref_known(v_____do__lift_2389_, 1);
        lean_inc(v_toBind_2382_);
        lean_inc(v_inst_2381_);
        lean_inc_ref(v_00_u03c6_2379_);
        v___f_2391_ = lean_alloc_closure(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__6___boxed
                as *mut core::ffi::c_void,
            20,
            19,
        );
        lean_closure_set(v___f_2391_, 0, v_toApplicative_2370_);
        lean_closure_set(v___f_2391_, 1, v___x_2371_);
        lean_closure_set(v___f_2391_, 2, v___x_2372_);
        lean_closure_set(v___f_2391_, 3, v___x_2373_);
        lean_closure_set(v___f_2391_, 4, v___x_2374_);
        lean_closure_set(v___f_2391_, 5, v___x_2375_);
        lean_closure_set(v___f_2391_, 6, v_00_u03c3s_2376_);
        lean_closure_set(v___f_2391_, 7, v_hyps_2377_);
        lean_closure_set(v___f_2391_, 8, v_target_2378_);
        lean_closure_set(v___f_2391_, 9, v_00_u03c6_2379_);
        lean_closure_set(v___f_2391_, 10, v_a_2390_);
        lean_closure_set(v___f_2391_, 11, v_u_2380_);
        lean_closure_set(v___f_2391_, 12, v_inst_2381_);
        lean_closure_set(v___f_2391_, 13, v_toBind_2382_);
        lean_closure_set(v___f_2391_, 14, v_kSuccess_2383_);
        lean_closure_set(v___f_2391_, 15, v_inst_2384_);
        lean_closure_set(v___f_2391_, 16, v_inst_2385_);
        lean_closure_set(v___f_2391_, 17, v_P_x27_2386_);
        lean_closure_set(v___f_2391_, 18, v_kFail_2387_);
        v___x_2392_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1;
        v___x_2393_ = l_Lean_mkConst(v___x_2392_, v___x_2388_);
        v___x_2394_ =
            lean_alloc_closure(l_Lean_Meta_isDefEq___boxed as *mut core::ffi::c_void, 7, 2);
        lean_closure_set(v___x_2394_, 0, v___x_2393_);
        lean_closure_set(v___x_2394_, 1, v_00_u03c6_2379_);
        v___x_2395_ = lean_apply_2(v_inst_2381_, lean_box(0), v___x_2394_);
        v___x_2396_ = lean_apply_4(
            v_toBind_2382_,
            lean_box(0),
            lean_box(0),
            v___x_2395_,
            v___f_2391_,
        );
        return v___x_2396_;
    } else {
        lean_dec(v_____do__lift_2389_);
        lean_dec(v___x_2388_);
        lean_dec_ref(v_P_x27_2386_);
        lean_dec_ref(v_inst_2385_);
        lean_dec_ref(v_inst_2384_);
        lean_dec(v_kSuccess_2383_);
        lean_dec(v_toBind_2382_);
        lean_dec(v_inst_2381_);
        lean_dec(v_u_2380_);
        lean_dec_ref(v_00_u03c6_2379_);
        lean_dec_ref(v_target_2378_);
        lean_dec_ref(v_hyps_2377_);
        lean_dec_ref(v_00_u03c3s_2376_);
        lean_dec(v___x_2375_);
        lean_dec_ref(v___x_2374_);
        lean_dec_ref(v___x_2373_);
        lean_dec_ref(v___x_2372_);
        lean_dec_ref(v___x_2371_);
        lean_dec_ref(v_toApplicative_2370_);
        return v_kFail_2387_;
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2397_: *mut LeanObject = *_args.add(0);
    let mut v___x_2398_: *mut LeanObject = *_args.add(1);
    let mut v___x_2399_: *mut LeanObject = *_args.add(2);
    let mut v___x_2400_: *mut LeanObject = *_args.add(3);
    let mut v___x_2401_: *mut LeanObject = *_args.add(4);
    let mut v___x_2402_: *mut LeanObject = *_args.add(5);
    let mut v_00_u03c3s_2403_: *mut LeanObject = *_args.add(6);
    let mut v_hyps_2404_: *mut LeanObject = *_args.add(7);
    let mut v_target_2405_: *mut LeanObject = *_args.add(8);
    let mut v_00_u03c6_2406_: *mut LeanObject = *_args.add(9);
    let mut v_u_2407_: *mut LeanObject = *_args.add(10);
    let mut v_inst_2408_: *mut LeanObject = *_args.add(11);
    let mut v_toBind_2409_: *mut LeanObject = *_args.add(12);
    let mut v_kSuccess_2410_: *mut LeanObject = *_args.add(13);
    let mut v_inst_2411_: *mut LeanObject = *_args.add(14);
    let mut v_inst_2412_: *mut LeanObject = *_args.add(15);
    let mut v_P_x27_2413_: *mut LeanObject = *_args.add(16);
    let mut v_kFail_2414_: *mut LeanObject = *_args.add(17);
    let mut v___x_2415_: *mut LeanObject = *_args.add(18);
    let mut v_____do__lift_2416_: *mut LeanObject = *_args.add(19);
    let mut v_res_2417_: *mut LeanObject = core::ptr::null_mut();
    v_res_2417_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7(
        v_toApplicative_2397_,
        v___x_2398_,
        v___x_2399_,
        v___x_2400_,
        v___x_2401_,
        v___x_2402_,
        v_00_u03c3s_2403_,
        v_hyps_2404_,
        v_target_2405_,
        v_00_u03c6_2406_,
        v_u_2407_,
        v_inst_2408_,
        v_toBind_2409_,
        v_kSuccess_2410_,
        v_inst_2411_,
        v_inst_2412_,
        v_P_x27_2413_,
        v_kFail_2414_,
        v___x_2415_,
        v_____do__lift_2416_,
    );
    return v_res_2417_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(
    mut v_toApplicative_2420_: *mut LeanObject,
    mut v___x_2421_: *mut LeanObject,
    mut v___x_2422_: *mut LeanObject,
    mut v___x_2423_: *mut LeanObject,
    mut v___x_2424_: *mut LeanObject,
    mut v_00_u03c3s_2425_: *mut LeanObject,
    mut v_hyps_2426_: *mut LeanObject,
    mut v_target_2427_: *mut LeanObject,
    mut v_00_u03c6_2428_: *mut LeanObject,
    mut v_u_2429_: *mut LeanObject,
    mut v_inst_2430_: *mut LeanObject,
    mut v_toBind_2431_: *mut LeanObject,
    mut v_kSuccess_2432_: *mut LeanObject,
    mut v_inst_2433_: *mut LeanObject,
    mut v_inst_2434_: *mut LeanObject,
    mut v_kFail_2435_: *mut LeanObject,
    mut v___x_2436_: *mut LeanObject,
    mut v_P_x27_2437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    v___x_2438_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0;
    lean_inc_ref(v_P_x27_2437_);
    lean_inc(v_toBind_2431_);
    lean_inc(v_inst_2430_);
    lean_inc_ref(v_00_u03c6_2428_);
    lean_inc_ref(v_hyps_2426_);
    lean_inc_ref(v_00_u03c3s_2425_);
    lean_inc(v___x_2424_);
    lean_inc_ref(v___x_2423_);
    lean_inc_ref(v___x_2422_);
    lean_inc_ref(v___x_2421_);
    v___f_2439_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___boxed
            as *mut core::ffi::c_void,
        20,
        19,
    );
    lean_closure_set(v___f_2439_, 0, v_toApplicative_2420_);
    lean_closure_set(v___f_2439_, 1, v___x_2421_);
    lean_closure_set(v___f_2439_, 2, v___x_2422_);
    lean_closure_set(v___f_2439_, 3, v___x_2423_);
    lean_closure_set(v___f_2439_, 4, v___x_2438_);
    lean_closure_set(v___f_2439_, 5, v___x_2424_);
    lean_closure_set(v___f_2439_, 6, v_00_u03c3s_2425_);
    lean_closure_set(v___f_2439_, 7, v_hyps_2426_);
    lean_closure_set(v___f_2439_, 8, v_target_2427_);
    lean_closure_set(v___f_2439_, 9, v_00_u03c6_2428_);
    lean_closure_set(v___f_2439_, 10, v_u_2429_);
    lean_closure_set(v___f_2439_, 11, v_inst_2430_);
    lean_closure_set(v___f_2439_, 12, v_toBind_2431_);
    lean_closure_set(v___f_2439_, 13, v_kSuccess_2432_);
    lean_closure_set(v___f_2439_, 14, v_inst_2433_);
    lean_closure_set(v___f_2439_, 15, v_inst_2434_);
    lean_closure_set(v___f_2439_, 16, v_P_x27_2437_);
    lean_closure_set(v___f_2439_, 17, v_kFail_2435_);
    lean_closure_set(v___f_2439_, 18, v___x_2436_);
    v___x_2440_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__1;
    v___x_2441_ = l_Lean_Name_mkStr5(
        v___x_2421_,
        v___x_2422_,
        v___x_2423_,
        v___x_2438_,
        v___x_2440_,
    );
    v___x_2442_ = l_Lean_mkConst(v___x_2441_, v___x_2424_);
    v___x_2443_ = l_Lean_mkApp4(
        v___x_2442_,
        v_00_u03c3s_2425_,
        v_hyps_2426_,
        v_P_x27_2437_,
        v_00_u03c6_2428_,
    );
    v___x_2444_ = lean_box(0);
    v___x_2445_ = lean_alloc_closure(
        l_Lean_Meta_trySynthInstance___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___x_2445_, 0, v___x_2443_);
    lean_closure_set(v___x_2445_, 1, v___x_2444_);
    v___x_2446_ = lean_apply_2(v_inst_2430_, lean_box(0), v___x_2445_);
    v___x_2447_ = lean_apply_4(
        v_toBind_2431_,
        lean_box(0),
        lean_box(0),
        v___x_2446_,
        v___f_2439_,
    );
    return v___x_2447_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2448_: *mut LeanObject = *_args.add(0);
    let mut v___x_2449_: *mut LeanObject = *_args.add(1);
    let mut v___x_2450_: *mut LeanObject = *_args.add(2);
    let mut v___x_2451_: *mut LeanObject = *_args.add(3);
    let mut v___x_2452_: *mut LeanObject = *_args.add(4);
    let mut v_00_u03c3s_2453_: *mut LeanObject = *_args.add(5);
    let mut v_hyps_2454_: *mut LeanObject = *_args.add(6);
    let mut v_target_2455_: *mut LeanObject = *_args.add(7);
    let mut v_00_u03c6_2456_: *mut LeanObject = *_args.add(8);
    let mut v_u_2457_: *mut LeanObject = *_args.add(9);
    let mut v_inst_2458_: *mut LeanObject = *_args.add(10);
    let mut v_toBind_2459_: *mut LeanObject = *_args.add(11);
    let mut v_kSuccess_2460_: *mut LeanObject = *_args.add(12);
    let mut v_inst_2461_: *mut LeanObject = *_args.add(13);
    let mut v_inst_2462_: *mut LeanObject = *_args.add(14);
    let mut v_kFail_2463_: *mut LeanObject = *_args.add(15);
    let mut v___x_2464_: *mut LeanObject = *_args.add(16);
    let mut v_P_x27_2465_: *mut LeanObject = *_args.add(17);
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v_res_2466_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8(
        v_toApplicative_2448_,
        v___x_2449_,
        v___x_2450_,
        v___x_2451_,
        v___x_2452_,
        v_00_u03c3s_2453_,
        v_hyps_2454_,
        v_target_2455_,
        v_00_u03c6_2456_,
        v_u_2457_,
        v_inst_2458_,
        v_toBind_2459_,
        v_kSuccess_2460_,
        v_inst_2461_,
        v_inst_2462_,
        v_kFail_2463_,
        v___x_2464_,
        v_P_x27_2465_,
    );
    return v_res_2466_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(
    mut v_u_2474_: *mut LeanObject,
    mut v_toApplicative_2475_: *mut LeanObject,
    mut v_00_u03c3s_2476_: *mut LeanObject,
    mut v_hyps_2477_: *mut LeanObject,
    mut v_target_2478_: *mut LeanObject,
    mut v_inst_2479_: *mut LeanObject,
    mut v_toBind_2480_: *mut LeanObject,
    mut v_kSuccess_2481_: *mut LeanObject,
    mut v_inst_2482_: *mut LeanObject,
    mut v_inst_2483_: *mut LeanObject,
    mut v_kFail_2484_: *mut LeanObject,
    mut v___x_2485_: u8,
    mut v___x_2486_: *mut LeanObject,
    mut v_00_u03c6_2487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut LeanObject = core::ptr::null_mut();
    v___x_2488_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0;
    v___x_2489_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1;
    v___x_2490_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2;
    v___x_2491_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3;
    v___x_2492_ = lean_box(0);
    lean_inc(v_u_2474_);
    v___x_2493_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2493_, 0, v_u_2474_);
    lean_ctor_set(v___x_2493_, 1, v___x_2492_);
    lean_inc(v_toBind_2480_);
    lean_inc(v_inst_2479_);
    lean_inc_ref(v_00_u03c3s_2476_);
    lean_inc_ref(v___x_2493_);
    v___f_2494_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___boxed
            as *mut core::ffi::c_void,
        18,
        17,
    );
    lean_closure_set(v___f_2494_, 0, v_toApplicative_2475_);
    lean_closure_set(v___f_2494_, 1, v___x_2488_);
    lean_closure_set(v___f_2494_, 2, v___x_2489_);
    lean_closure_set(v___f_2494_, 3, v___x_2490_);
    lean_closure_set(v___f_2494_, 4, v___x_2493_);
    lean_closure_set(v___f_2494_, 5, v_00_u03c3s_2476_);
    lean_closure_set(v___f_2494_, 6, v_hyps_2477_);
    lean_closure_set(v___f_2494_, 7, v_target_2478_);
    lean_closure_set(v___f_2494_, 8, v_00_u03c6_2487_);
    lean_closure_set(v___f_2494_, 9, v_u_2474_);
    lean_closure_set(v___f_2494_, 10, v_inst_2479_);
    lean_closure_set(v___f_2494_, 11, v_toBind_2480_);
    lean_closure_set(v___f_2494_, 12, v_kSuccess_2481_);
    lean_closure_set(v___f_2494_, 13, v_inst_2482_);
    lean_closure_set(v___f_2494_, 14, v_inst_2483_);
    lean_closure_set(v___f_2494_, 15, v_kFail_2484_);
    lean_closure_set(v___f_2494_, 16, v___x_2492_);
    v___x_2495_ = l_Lean_mkConst(v___x_2491_, v___x_2493_);
    v___x_2496_ = l_Lean_Expr_app___override(v___x_2495_, v_00_u03c3s_2476_);
    v___x_2497_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2497_, 0, v___x_2496_);
    v___x_2498_ = lean_box((v___x_2485_) as usize);
    v___x_2499_ = lean_alloc_closure(
        l_Lean_Meta_mkFreshExprMVar___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_2499_, 0, v___x_2497_);
    lean_closure_set(v___x_2499_, 1, v___x_2498_);
    lean_closure_set(v___x_2499_, 2, v___x_2486_);
    v___x_2500_ = lean_apply_2(v_inst_2479_, lean_box(0), v___x_2499_);
    v___x_2501_ = lean_apply_4(
        v_toBind_2480_,
        lean_box(0),
        lean_box(0),
        v___x_2500_,
        v___f_2494_,
    );
    return v___x_2501_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed(
    mut v_u_2502_: *mut LeanObject,
    mut v_toApplicative_2503_: *mut LeanObject,
    mut v_00_u03c3s_2504_: *mut LeanObject,
    mut v_hyps_2505_: *mut LeanObject,
    mut v_target_2506_: *mut LeanObject,
    mut v_inst_2507_: *mut LeanObject,
    mut v_toBind_2508_: *mut LeanObject,
    mut v_kSuccess_2509_: *mut LeanObject,
    mut v_inst_2510_: *mut LeanObject,
    mut v_inst_2511_: *mut LeanObject,
    mut v_kFail_2512_: *mut LeanObject,
    mut v___x_2513_: *mut LeanObject,
    mut v___x_2514_: *mut LeanObject,
    mut v_00_u03c6_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_813__boxed_2516_: u8 = 0;
    let mut v_res_2517_: *mut LeanObject = core::ptr::null_mut();
    v___x_813__boxed_2516_ = (lean_unbox(v___x_2513_) as u8);
    v_res_2517_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9(
        v_u_2502_,
        v_toApplicative_2503_,
        v_00_u03c3s_2504_,
        v_hyps_2505_,
        v_target_2506_,
        v_inst_2507_,
        v_toBind_2508_,
        v_kSuccess_2509_,
        v_inst_2510_,
        v_inst_2511_,
        v_kFail_2512_,
        v___x_813__boxed_2516_,
        v___x_2514_,
        v_00_u03c6_2515_,
    );
    return v_res_2517_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    v___x_2518_ = lean_box(0);
    v___x_2519_ = l_Lean_mkSort(v___x_2518_);
    return v___x_2519_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2520_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__0,
    );
    v___x_2521_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2521_, 0, v___x_2520_);
    return v___x_2521_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: u8 = 0;
    let mut v___x_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    v___x_2522_ = lean_box(0);
    v___x_2523_ = 0;
    v___x_2524_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1,
    );
    v___x_2525_ = lean_box((v___x_2523_) as usize);
    v___x_2526_ = lean_alloc_closure(
        l_Lean_Meta_mkFreshExprMVar___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___x_2526_, 0, v___x_2524_);
    lean_closure_set(v___x_2526_, 1, v___x_2525_);
    lean_closure_set(v___x_2526_, 2, v___x_2522_);
    return v___x_2526_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(
    mut v_inst_2527_: *mut LeanObject,
    mut v_inst_2528_: *mut LeanObject,
    mut v_inst_2529_: *mut LeanObject,
    mut v_goal_2530_: *mut LeanObject,
    mut v_kFail_2531_: *mut LeanObject,
    mut v_kSuccess_2532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: *mut LeanObject = core::ptr::null_mut();
    v_u_2533_ = lean_ctor_get(v_goal_2530_, 0);
    lean_inc(v_u_2533_);
    v_00_u03c3s_2534_ = lean_ctor_get(v_goal_2530_, 1);
    lean_inc_ref(v_00_u03c3s_2534_);
    v_hyps_2535_ = lean_ctor_get(v_goal_2530_, 2);
    lean_inc_ref(v_hyps_2535_);
    v_target_2536_ = lean_ctor_get(v_goal_2530_, 3);
    lean_inc_ref(v_target_2536_);
    lean_dec_ref(v_goal_2530_);
    v_toApplicative_2537_ = lean_ctor_get(v_inst_2527_, 0);
    lean_inc_ref(v_toApplicative_2537_);
    v_toBind_2538_ = lean_ctor_get(v_inst_2527_, 1);
    lean_inc_n(v_toBind_2538_, 2);
    v___x_2539_ = 0;
    v___x_2540_ = lean_box(0);
    v___x_2541_ = lean_box((v___x_2539_) as usize);
    lean_inc(v_inst_2529_);
    v___f_2542_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___boxed
            as *mut core::ffi::c_void,
        14,
        13,
    );
    lean_closure_set(v___f_2542_, 0, v_u_2533_);
    lean_closure_set(v___f_2542_, 1, v_toApplicative_2537_);
    lean_closure_set(v___f_2542_, 2, v_00_u03c3s_2534_);
    lean_closure_set(v___f_2542_, 3, v_hyps_2535_);
    lean_closure_set(v___f_2542_, 4, v_target_2536_);
    lean_closure_set(v___f_2542_, 5, v_inst_2529_);
    lean_closure_set(v___f_2542_, 6, v_toBind_2538_);
    lean_closure_set(v___f_2542_, 7, v_kSuccess_2532_);
    lean_closure_set(v___f_2542_, 8, v_inst_2528_);
    lean_closure_set(v___f_2542_, 9, v_inst_2527_);
    lean_closure_set(v___f_2542_, 10, v_kFail_2531_);
    lean_closure_set(v___f_2542_, 11, v___x_2541_);
    lean_closure_set(v___f_2542_, 12, v___x_2540_);
    v___x_2543_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__2,
    );
    v___x_2544_ = lean_apply_2(v_inst_2529_, lean_box(0), v___x_2543_);
    v___x_2545_ = lean_apply_4(
        v_toBind_2538_,
        lean_box(0),
        lean_box(0),
        v___x_2544_,
        v___f_2542_,
    );
    return v___x_2545_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore(
    mut v_m_2546_: *mut LeanObject,
    mut v_inst_2547_: *mut LeanObject,
    mut v_inst_2548_: *mut LeanObject,
    mut v_inst_2549_: *mut LeanObject,
    mut v_goal_2550_: *mut LeanObject,
    mut v_kFail_2551_: *mut LeanObject,
    mut v_kSuccess_2552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    v___x_2553_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(
        v_inst_2547_,
        v_inst_2548_,
        v_inst_2549_,
        v_goal_2550_,
        v_kFail_2551_,
        v_kSuccess_2552_,
    );
    return v___x_2553_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(
    mut v_k_2554_: *mut LeanObject,
    mut v_x_2555_: *mut LeanObject,
    mut v_x_2556_: *mut LeanObject,
    mut v_goal_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    v___x_2558_ = lean_apply_1(v_k_2554_, v_goal_2557_);
    return v___x_2558_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed(
    mut v_k_2559_: *mut LeanObject,
    mut v_x_2560_: *mut LeanObject,
    mut v_x_2561_: *mut LeanObject,
    mut v_goal_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2563_: *mut LeanObject = core::ptr::null_mut();
    v_res_2563_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0(
        v_k_2559_,
        v_x_2560_,
        v_x_2561_,
        v_goal_2562_,
    );
    lean_dec_ref(v_x_2561_);
    lean_dec_ref(v_x_2560_);
    return v_res_2563_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(
    mut v_inst_2564_: *mut LeanObject,
    mut v_inst_2565_: *mut LeanObject,
    mut v_inst_2566_: *mut LeanObject,
    mut v_goal_2567_: *mut LeanObject,
    mut v_k_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_k_2568_);
    v___f_2569_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2569_, 0, v_k_2568_);
    lean_inc_ref(v_goal_2567_);
    v___x_2570_ = lean_apply_1(v_k_2568_, v_goal_2567_);
    v___x_2571_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg(
        v_inst_2564_,
        v_inst_2565_,
        v_inst_2566_,
        v_goal_2567_,
        v___x_2570_,
        v___f_2569_,
    );
    return v___x_2571_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame(
    mut v_m_2572_: *mut LeanObject,
    mut v_inst_2573_: *mut LeanObject,
    mut v_inst_2574_: *mut LeanObject,
    mut v_inst_2575_: *mut LeanObject,
    mut v_goal_2576_: *mut LeanObject,
    mut v_k_2577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    v___x_2578_ = l_Lean_Elab_Tactic_Do_ProofMode_mTryFrame___redArg(
        v_inst_2573_,
        v_inst_2574_,
        v_inst_2575_,
        v_goal_2576_,
        v_k_2577_,
    );
    return v___x_2578_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(
    mut v_e_2579_: *mut LeanObject,
    mut v___y_2580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2582_: u8 = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2596_: u8 = 0;
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut v_unused_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2582_ = l_Lean_Expr_hasMVar(v_e_2579_);
                if v___x_2582_ == 0 {
                    v___x_2583_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2583_, 0, v_e_2579_);
                    return v___x_2583_;
                } else {
                    v___x_2584_ = lean_st_ref_get(v___y_2580_);
                    v_mctx_2585_ = lean_ctor_get(v___x_2584_, 0);
                    lean_inc_ref(v_mctx_2585_);
                    lean_dec(v___x_2584_);
                    v___x_2586_ = l_Lean_instantiateMVarsCore(v_mctx_2585_, v_e_2579_);
                    v_fst_2587_ = lean_ctor_get(v___x_2586_, 0);
                    lean_inc(v_fst_2587_);
                    v_snd_2588_ = lean_ctor_get(v___x_2586_, 1);
                    lean_inc(v_snd_2588_);
                    lean_dec_ref(v___x_2586_);
                    v___x_2589_ = lean_st_ref_take(v___y_2580_);
                    v_cache_2590_ = lean_ctor_get(v___x_2589_, 1);
                    v_zetaDeltaFVarIds_2591_ = lean_ctor_get(v___x_2589_, 2);
                    v_postponed_2592_ = lean_ctor_get(v___x_2589_, 3);
                    v_diag_2593_ = lean_ctor_get(v___x_2589_, 4);
                    v_isSharedCheck_2602_ = (!lean_is_exclusive(v___x_2589_)) as u8;
                    if v_isSharedCheck_2602_ == 0 {
                        v_unused_2603_ = lean_ctor_get(v___x_2589_, 0);
                        lean_dec(v_unused_2603_);
                        v___x_2595_ = v___x_2589_;
                        v_isShared_2596_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_2593_);
                        lean_inc(v_postponed_2592_);
                        lean_inc(v_zetaDeltaFVarIds_2591_);
                        lean_inc(v_cache_2590_);
                        lean_dec(v___x_2589_);
                        v___x_2595_ = lean_box(0);
                        v_isShared_2596_ = v_isSharedCheck_2602_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2596_ == 0 {
                    lean_ctor_set(v___x_2595_, 0, v_snd_2588_);
                    v___x_2598_ = v___x_2595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_snd_2588_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_cache_2590_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 2, v_zetaDeltaFVarIds_2591_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 3, v_postponed_2592_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 4, v_diag_2593_);
                    v___x_2598_ = v_reuseFailAlloc_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2599_ = lean_st_ref_set(v___y_2580_, v___x_2598_);
                v___x_2600_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2600_, 0, v_fst_2587_);
                return v___x_2600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg___boxed(
    mut v_e_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
    mut v___y_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2607_: *mut LeanObject = core::ptr::null_mut();
    v_res_2607_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(
            v_e_2604_,
            v___y_2605_,
        );
    lean_dec(v___y_2605_);
    return v_res_2607_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(
    mut v_e_2608_: *mut LeanObject,
    mut v___y_2609_: *mut LeanObject,
    mut v___y_2610_: *mut LeanObject,
    mut v___y_2611_: *mut LeanObject,
    mut v___y_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    v___x_2618_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(
            v_e_2608_,
            v___y_2614_,
        );
    return v___x_2618_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___boxed(
    mut v_e_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
    mut v___y_2625_: *mut LeanObject,
    mut v___y_2626_: *mut LeanObject,
    mut v___y_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2629_: *mut LeanObject = core::ptr::null_mut();
    v_res_2629_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1(
        v_e_2619_,
        v___y_2620_,
        v___y_2621_,
        v___y_2622_,
        v___y_2623_,
        v___y_2624_,
        v___y_2625_,
        v___y_2626_,
        v___y_2627_,
    );
    lean_dec(v___y_2627_);
    lean_dec_ref(v___y_2626_);
    lean_dec(v___y_2625_);
    lean_dec_ref(v___y_2624_);
    lean_dec(v___y_2623_);
    lean_dec_ref(v___y_2622_);
    lean_dec(v___y_2621_);
    lean_dec_ref(v___y_2620_);
    return v_res_2629_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(
    mut v_x_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_2634_);
    lean_inc_ref(v___y_2633_);
    lean_inc(v___y_2632_);
    lean_inc_ref(v___y_2631_);
    v___x_2640_ = lean_apply_9(
        v_x_2630_,
        v___y_2631_,
        v___y_2632_,
        v___y_2633_,
        v___y_2634_,
        v___y_2635_,
        v___y_2636_,
        v___y_2637_,
        v___y_2638_,
        lean_box(0),
    );
    return v___x_2640_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed(
    mut v_x_2641_: *mut LeanObject,
    mut v___y_2642_: *mut LeanObject,
    mut v___y_2643_: *mut LeanObject,
    mut v___y_2644_: *mut LeanObject,
    mut v___y_2645_: *mut LeanObject,
    mut v___y_2646_: *mut LeanObject,
    mut v___y_2647_: *mut LeanObject,
    mut v___y_2648_: *mut LeanObject,
    mut v___y_2649_: *mut LeanObject,
    mut v___y_2650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2651_: *mut LeanObject = core::ptr::null_mut();
    v_res_2651_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0(v_x_2641_, v___y_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_, v___y_2647_, v___y_2648_, v___y_2649_);
    lean_dec(v___y_2645_);
    lean_dec_ref(v___y_2644_);
    lean_dec(v___y_2643_);
    lean_dec_ref(v___y_2642_);
    return v_res_2651_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(
    mut v_mvarId_2652_: *mut LeanObject,
    mut v_x_2653_: *mut LeanObject,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
    mut v___y_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
    mut v___y_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
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
                lean_inc(v___y_2657_);
                lean_inc_ref(v___y_2656_);
                lean_inc(v___y_2655_);
                lean_inc_ref(v___y_2654_);
                v___f_2663_ = lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                lean_closure_set(v___f_2663_, 0, v_x_2653_);
                lean_closure_set(v___f_2663_, 1, v___y_2654_);
                lean_closure_set(v___f_2663_, 2, v___y_2655_);
                lean_closure_set(v___f_2663_, 3, v___y_2656_);
                lean_closure_set(v___f_2663_, 4, v___y_2657_);
                v___x_2664_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_2652_,
                    v___f_2663_,
                    v___y_2658_,
                    v___y_2659_,
                    v___y_2660_,
                    v___y_2661_,
                );
                if lean_obj_tag(v___x_2664_) == 0 {
                    return v___x_2664_;
                } else {
                    v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
                    v_isSharedCheck_2672_ = (!lean_is_exclusive(v___x_2664_)) as u8;
                    if v_isSharedCheck_2672_ == 0 {
                        v___x_2667_ = v___x_2664_;
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2665_);
                        lean_dec(v___x_2664_);
                        v___x_2667_ = lean_box(0);
                        v_isShared_2668_ = v_isSharedCheck_2672_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2668_ == 0 {
                    v___x_2670_ = v___x_2667_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2671_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2671_, 0, v_a_2665_);
                    v___x_2670_ = v_reuseFailAlloc_2671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg___boxed(
    mut v_mvarId_2673_: *mut LeanObject,
    mut v_x_2674_: *mut LeanObject,
    mut v___y_2675_: *mut LeanObject,
    mut v___y_2676_: *mut LeanObject,
    mut v___y_2677_: *mut LeanObject,
    mut v___y_2678_: *mut LeanObject,
    mut v___y_2679_: *mut LeanObject,
    mut v___y_2680_: *mut LeanObject,
    mut v___y_2681_: *mut LeanObject,
    mut v___y_2682_: *mut LeanObject,
    mut v___y_2683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2684_: *mut LeanObject = core::ptr::null_mut();
    v_res_2684_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_2673_, v_x_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_, v___y_2682_);
    lean_dec(v___y_2682_);
    lean_dec_ref(v___y_2681_);
    lean_dec(v___y_2680_);
    lean_dec_ref(v___y_2679_);
    lean_dec(v___y_2678_);
    lean_dec_ref(v___y_2677_);
    lean_dec(v___y_2676_);
    lean_dec_ref(v___y_2675_);
    return v_res_2684_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(
    mut v_00_u03b1_2685_: *mut LeanObject,
    mut v_mvarId_2686_: *mut LeanObject,
    mut v_x_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
    mut v___y_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
    mut v___y_2693_: *mut LeanObject,
    mut v___y_2694_: *mut LeanObject,
    mut v___y_2695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    v___x_2697_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_mvarId_2686_, v_x_2687_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
    return v___x_2697_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___boxed(
    mut v_00_u03b1_2698_: *mut LeanObject,
    mut v_mvarId_2699_: *mut LeanObject,
    mut v_x_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
    mut v___y_2703_: *mut LeanObject,
    mut v___y_2704_: *mut LeanObject,
    mut v___y_2705_: *mut LeanObject,
    mut v___y_2706_: *mut LeanObject,
    mut v___y_2707_: *mut LeanObject,
    mut v___y_2708_: *mut LeanObject,
    mut v___y_2709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2710_: *mut LeanObject = core::ptr::null_mut();
    v_res_2710_ =
        l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5(
            v_00_u03b1_2698_,
            v_mvarId_2699_,
            v_x_2700_,
            v___y_2701_,
            v___y_2702_,
            v___y_2703_,
            v___y_2704_,
            v___y_2705_,
            v___y_2706_,
            v___y_2707_,
            v___y_2708_,
        );
    lean_dec(v___y_2708_);
    lean_dec_ref(v___y_2707_);
    lean_dec(v___y_2706_);
    lean_dec_ref(v___y_2705_);
    lean_dec(v___y_2704_);
    lean_dec_ref(v___y_2703_);
    lean_dec(v___y_2702_);
    lean_dec_ref(v___y_2701_);
    return v_res_2710_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(
    mut v_msgData_2711_: *mut LeanObject,
    mut v___y_2712_: *mut LeanObject,
    mut v___y_2713_: *mut LeanObject,
    mut v___y_2714_: *mut LeanObject,
    mut v___y_2715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___x_2717_ = lean_st_ref_get(v___y_2715_);
    v_env_2718_ = lean_ctor_get(v___x_2717_, 0);
    lean_inc_ref(v_env_2718_);
    lean_dec(v___x_2717_);
    v___x_2719_ = lean_st_ref_get(v___y_2713_);
    v_mctx_2720_ = lean_ctor_get(v___x_2719_, 0);
    lean_inc_ref(v_mctx_2720_);
    lean_dec(v___x_2719_);
    v_lctx_2721_ = lean_ctor_get(v___y_2712_, 2);
    v_options_2722_ = lean_ctor_get(v___y_2714_, 2);
    lean_inc_ref(v_options_2722_);
    lean_inc_ref(v_lctx_2721_);
    v___x_2723_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2723_, 0, v_env_2718_);
    lean_ctor_set(v___x_2723_, 1, v_mctx_2720_);
    lean_ctor_set(v___x_2723_, 2, v_lctx_2721_);
    lean_ctor_set(v___x_2723_, 3, v_options_2722_);
    v___x_2724_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2724_, 0, v___x_2723_);
    lean_ctor_set(v___x_2724_, 1, v_msgData_2711_);
    v___x_2725_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2725_, 0, v___x_2724_);
    return v___x_2725_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0___boxed(
    mut v_msgData_2726_: *mut LeanObject,
    mut v___y_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2732_: *mut LeanObject = core::ptr::null_mut();
    v_res_2732_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msgData_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
    lean_dec(v___y_2730_);
    lean_dec_ref(v___y_2729_);
    lean_dec(v___y_2728_);
    lean_dec_ref(v___y_2727_);
    return v_res_2732_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(
    mut v_msg_2733_: *mut LeanObject,
    mut v___y_2734_: *mut LeanObject,
    mut v___y_2735_: *mut LeanObject,
    mut v___y_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2744_: u8 = 0;
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2739_ = lean_ctor_get(v___y_2736_, 5);
                v___x_2740_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
                v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
                v_isSharedCheck_2749_ = (!lean_is_exclusive(v___x_2740_)) as u8;
                if v_isSharedCheck_2749_ == 0 {
                    v___x_2743_ = v___x_2740_;
                    v_isShared_2744_ = v_isSharedCheck_2749_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2741_);
                    lean_dec(v___x_2740_);
                    v___x_2743_ = lean_box(0);
                    v_isShared_2744_ = v_isSharedCheck_2749_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2739_);
                v___x_2745_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2745_, 0, v_ref_2739_);
                lean_ctor_set(v___x_2745_, 1, v_a_2741_);
                if v_isShared_2744_ == 0 {
                    lean_ctor_set_tag(v___x_2743_, 1);
                    lean_ctor_set(v___x_2743_, 0, v___x_2745_);
                    v___x_2747_ = v___x_2743_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
                    v___x_2747_ = v_reuseFailAlloc_2748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg___boxed(
    mut v_msg_2750_: *mut LeanObject,
    mut v___y_2751_: *mut LeanObject,
    mut v___y_2752_: *mut LeanObject,
    mut v___y_2753_: *mut LeanObject,
    mut v___y_2754_: *mut LeanObject,
    mut v___y_2755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2756_: *mut LeanObject = core::ptr::null_mut();
    v_res_2756_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(
            v_msg_2750_,
            v___y_2751_,
            v___y_2752_,
            v___y_2753_,
            v___y_2754_,
        );
    lean_dec(v___y_2754_);
    lean_dec_ref(v___y_2753_);
    lean_dec(v___y_2752_);
    lean_dec_ref(v___y_2751_);
    return v_res_2756_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    v___x_2758_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__0;
    v___x_2759_ = l_Lean_stringToMessageData(v___x_2758_);
    return v___x_2759_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(
    mut v_x_2760_: *mut LeanObject,
    mut v___y_2761_: *mut LeanObject,
    mut v___y_2762_: *mut LeanObject,
    mut v___y_2763_: *mut LeanObject,
    mut v___y_2764_: *mut LeanObject,
    mut v___y_2765_: *mut LeanObject,
    mut v___y_2766_: *mut LeanObject,
    mut v___y_2767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    v___x_2769_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1_once
        ),
        _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___closed__1,
    );
    v___x_2770_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(
            v___x_2769_,
            v___y_2764_,
            v___y_2765_,
            v___y_2766_,
            v___y_2767_,
        );
    return v___x_2770_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0___boxed(
    mut v_x_2771_: *mut LeanObject,
    mut v___y_2772_: *mut LeanObject,
    mut v___y_2773_: *mut LeanObject,
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2780_: *mut LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__0(
        v_x_2771_,
        v___y_2772_,
        v___y_2773_,
        v___y_2774_,
        v___y_2775_,
        v___y_2776_,
        v___y_2777_,
        v___y_2778_,
    );
    lean_dec(v___y_2778_);
    lean_dec_ref(v___y_2777_);
    lean_dec(v___y_2776_);
    lean_dec_ref(v___y_2775_);
    lean_dec(v___y_2774_);
    lean_dec_ref(v___y_2773_);
    lean_dec(v___y_2772_);
    lean_dec_ref(v_x_2771_);
    return v_res_2780_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(
    mut v_x_2781_: *mut LeanObject,
    mut v_x_2782_: *mut LeanObject,
    mut v_goal_2783_: *mut LeanObject,
    mut v___y_2784_: *mut LeanObject,
    mut v___y_2785_: *mut LeanObject,
    mut v___y_2786_: *mut LeanObject,
    mut v___y_2787_: *mut LeanObject,
    mut v___y_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
    mut v___y_2791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2803_: u8 = 0;
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_unused_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2793_ = l_Lean_Elab_Tactic_Do_ProofMode_MGoal_toExpr(v_goal_2783_);
                v___x_2794_ = lean_box(0);
                v___x_2795_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
                    v___x_2793_,
                    v___x_2794_,
                    v___y_2788_,
                    v___y_2789_,
                    v___y_2790_,
                    v___y_2791_,
                );
                if lean_obj_tag(v___x_2795_) == 0 {
                    v_a_2796_ = lean_ctor_get(v___x_2795_, 0);
                    lean_inc(v_a_2796_);
                    lean_dec_ref_known(v___x_2795_, 1);
                    v___x_2797_ = l_Lean_Expr_mvarId_x21(v_a_2796_);
                    v___x_2798_ = lean_box(0);
                    v___x_2799_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2799_, 0, v___x_2797_);
                    lean_ctor_set(v___x_2799_, 1, v___x_2798_);
                    v___x_2800_ = l_Lean_Elab_Tactic_replaceMainGoal___redArg(
                        v___x_2799_,
                        v___y_2785_,
                        v___y_2788_,
                        v___y_2789_,
                        v___y_2790_,
                        v___y_2791_,
                    );
                    if lean_obj_tag(v___x_2800_) == 0 {
                        v_isSharedCheck_2807_ = (!lean_is_exclusive(v___x_2800_)) as u8;
                        if v_isSharedCheck_2807_ == 0 {
                            v_unused_2808_ = lean_ctor_get(v___x_2800_, 0);
                            lean_dec(v_unused_2808_);
                            v___x_2802_ = v___x_2800_;
                            v_isShared_2803_ = v_isSharedCheck_2807_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2800_);
                            v___x_2802_ = lean_box(0);
                            v_isShared_2803_ = v_isSharedCheck_2807_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2796_);
                        v_a_2809_ = lean_ctor_get(v___x_2800_, 0);
                        v_isSharedCheck_2816_ = (!lean_is_exclusive(v___x_2800_)) as u8;
                        if v_isSharedCheck_2816_ == 0 {
                            v___x_2811_ = v___x_2800_;
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2809_);
                            lean_dec(v___x_2800_);
                            v___x_2811_ = lean_box(0);
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    return v___x_2795_;
                }
            }
            1 => {
                if v_isShared_2803_ == 0 {
                    lean_ctor_set(v___x_2802_, 0, v_a_2796_);
                    v___x_2805_ = v___x_2802_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2796_);
                    v___x_2805_ = v_reuseFailAlloc_2806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2805_;
            }
            3 => {
                if v_isShared_2812_ == 0 {
                    v___x_2814_ = v___x_2811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
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
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1___boxed(
    mut v_x_2817_: *mut LeanObject,
    mut v_x_2818_: *mut LeanObject,
    mut v_goal_2819_: *mut LeanObject,
    mut v___y_2820_: *mut LeanObject,
    mut v___y_2821_: *mut LeanObject,
    mut v___y_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
    mut v___y_2824_: *mut LeanObject,
    mut v___y_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
    mut v___y_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2829_: *mut LeanObject = core::ptr::null_mut();
    v_res_2829_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__1(
        v_x_2817_,
        v_x_2818_,
        v_goal_2819_,
        v___y_2820_,
        v___y_2821_,
        v___y_2822_,
        v___y_2823_,
        v___y_2824_,
        v___y_2825_,
        v___y_2826_,
        v___y_2827_,
    );
    lean_dec(v___y_2827_);
    lean_dec_ref(v___y_2826_);
    lean_dec(v___y_2825_);
    lean_dec_ref(v___y_2824_);
    lean_dec(v___y_2823_);
    lean_dec_ref(v___y_2822_);
    lean_dec(v___y_2821_);
    lean_dec_ref(v___y_2820_);
    lean_dec_ref(v_x_2818_);
    lean_dec_ref(v_x_2817_);
    return v_res_2829_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(
    mut v_x_2830_: *mut LeanObject,
    mut v_x_2831_: *mut LeanObject,
    mut v_x_2832_: *mut LeanObject,
    mut v_x_2833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2838_: u8 = 0;
    let mut v___x_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: u8 = 0;
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: u8 = 0;
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2834_ = lean_ctor_get(v_x_2830_, 0);
                v_vs_2835_ = lean_ctor_get(v_x_2830_, 1);
                v_isSharedCheck_2859_ = (!lean_is_exclusive(v_x_2830_)) as u8;
                if v_isSharedCheck_2859_ == 0 {
                    v___x_2837_ = v_x_2830_;
                    v_isShared_2838_ = v_isSharedCheck_2859_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2835_);
                    lean_inc(v_ks_2834_);
                    lean_dec(v_x_2830_);
                    v___x_2837_ = lean_box(0);
                    v_isShared_2838_ = v_isSharedCheck_2859_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2839_ = lean_array_get_size(v_ks_2834_);
                v___x_2840_ = lean_nat_dec_lt(v_x_2831_, v___x_2839_);
                if v___x_2840_ == 0 {
                    lean_dec(v_x_2831_);
                    v___x_2841_ = lean_array_push(v_ks_2834_, v_x_2832_);
                    v___x_2842_ = lean_array_push(v_vs_2835_, v_x_2833_);
                    if v_isShared_2838_ == 0 {
                        lean_ctor_set(v___x_2837_, 1, v___x_2842_);
                        lean_ctor_set(v___x_2837_, 0, v___x_2841_);
                        v___x_2844_ = v___x_2837_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2841_);
                        lean_ctor_set(v_reuseFailAlloc_2845_, 1, v___x_2842_);
                        v___x_2844_ = v_reuseFailAlloc_2845_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2846_ = lean_array_fget_borrowed(v_ks_2834_, v_x_2831_);
                    v___x_2847_ = l_Lean_instBEqMVarId_beq(v_x_2832_, v_k_x27_2846_);
                    if v___x_2847_ == 0 {
                        if v_isShared_2838_ == 0 {
                            v___x_2849_ = v___x_2837_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_ks_2834_);
                            lean_ctor_set(v_reuseFailAlloc_2853_, 1, v_vs_2835_);
                            v___x_2849_ = v_reuseFailAlloc_2853_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2854_ = lean_array_fset(v_ks_2834_, v_x_2831_, v_x_2832_);
                        v___x_2855_ = lean_array_fset(v_vs_2835_, v_x_2831_, v_x_2833_);
                        lean_dec(v_x_2831_);
                        if v_isShared_2838_ == 0 {
                            lean_ctor_set(v___x_2837_, 1, v___x_2855_);
                            lean_ctor_set(v___x_2837_, 0, v___x_2854_);
                            v___x_2857_ = v___x_2837_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2854_);
                            lean_ctor_set(v_reuseFailAlloc_2858_, 1, v___x_2855_);
                            v___x_2857_ = v_reuseFailAlloc_2858_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2844_;
            }
            3 => {
                v___x_2850_ = lean_unsigned_to_nat(1);
                v___x_2851_ = lean_nat_add(v_x_2831_, v___x_2850_);
                lean_dec(v_x_2831_);
                v_x_2830_ = v___x_2849_;
                v_x_2831_ = v___x_2851_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2857_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(
    mut v_n_2860_: *mut LeanObject,
    mut v_k_2861_: *mut LeanObject,
    mut v_v_2862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    v___x_2863_ = lean_unsigned_to_nat(0);
    v___x_2864_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_n_2860_, v___x_2863_, v_k_2861_, v_v_2862_);
    return v___x_2864_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0()
-> usize {
    let mut v___x_2865_: usize = 0;
    let mut v___x_2866_: usize = 0;
    let mut v___x_2867_: usize = 0;
    v___x_2865_ = 5usize;
    v___x_2866_ = 1usize;
    v___x_2867_ = lean_usize_shift_left(v___x_2866_, v___x_2865_);
    return v___x_2867_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__1()
-> usize {
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: usize = 0;
    let mut v___x_2870_: usize = 0;
    v___x_2868_ = 1usize;
    v___x_2869_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__0);
    v___x_2870_ = lean_usize_sub(v___x_2869_, v___x_2868_);
    return v___x_2870_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    v___x_2871_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2871_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(
    mut v_x_2872_: *mut LeanObject,
    mut v_x_2873_: usize,
    mut v_x_2874_: usize,
    mut v_x_2875_: *mut LeanObject,
    mut v_x_2876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: usize = 0;
    let mut v___x_2879_: usize = 0;
    let mut v___x_2880_: usize = 0;
    let mut v___x_2881_: usize = 0;
    let mut v_j_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: u8 = 0;
    let mut v___x_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2887_: u8 = 0;
    let mut v_v_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2901_: u8 = 0;
    let mut v___x_2902_: u8 = 0;
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut v_node_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2913_: usize = 0;
    let mut v___x_2914_: usize = 0;
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2919_: u8 = 0;
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v_unused_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2927_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2932_: u8 = 0;
    let mut v_ks_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: usize = 0;
    let mut v___x_2939_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: u8 = 0;
    let mut v_reuseFailAlloc_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2944_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2872_) == 0 {
                    v_es_2877_ = lean_ctor_get(v_x_2872_, 0);
                    v___x_2878_ = 5usize;
                    v___x_2879_ = 1usize;
                    v___x_2880_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__1);
                    v___x_2881_ = lean_usize_land(v_x_2873_, v___x_2880_);
                    v_j_2882_ = lean_usize_to_nat(v___x_2881_);
                    v___x_2883_ = lean_array_get_size(v_es_2877_);
                    v___x_2884_ = lean_nat_dec_lt(v_j_2882_, v___x_2883_);
                    if v___x_2884_ == 0 {
                        lean_dec(v_j_2882_);
                        lean_dec(v_x_2876_);
                        lean_dec(v_x_2875_);
                        return v_x_2872_;
                    } else {
                        lean_inc_ref(v_es_2877_);
                        v_isSharedCheck_2921_ = (!lean_is_exclusive(v_x_2872_)) as u8;
                        if v_isSharedCheck_2921_ == 0 {
                            v_unused_2922_ = lean_ctor_get(v_x_2872_, 0);
                            lean_dec(v_unused_2922_);
                            v___x_2886_ = v_x_2872_;
                            v_isShared_2887_ = v_isSharedCheck_2921_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2872_);
                            v___x_2886_ = lean_box(0);
                            v_isShared_2887_ = v_isSharedCheck_2921_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2923_ = lean_ctor_get(v_x_2872_, 0);
                    v_vs_2924_ = lean_ctor_get(v_x_2872_, 1);
                    v_isSharedCheck_2944_ = (!lean_is_exclusive(v_x_2872_)) as u8;
                    if v_isSharedCheck_2944_ == 0 {
                        v___x_2926_ = v_x_2872_;
                        v_isShared_2927_ = v_isSharedCheck_2944_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2924_);
                        lean_inc(v_ks_2923_);
                        lean_dec(v_x_2872_);
                        v___x_2926_ = lean_box(0);
                        v_isShared_2927_ = v_isSharedCheck_2944_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2888_ = lean_array_fget(v_es_2877_, v_j_2882_);
                v___x_2889_ = lean_box(0);
                v_xs_x27_2890_ = lean_array_fset(v_es_2877_, v_j_2882_, v___x_2889_);
                match lean_obj_tag(v_v_2888_) {
                    0 => {
                        v_key_2897_ = lean_ctor_get(v_v_2888_, 0);
                        v_val_2898_ = lean_ctor_get(v_v_2888_, 1);
                        v_isSharedCheck_2908_ = (!lean_is_exclusive(v_v_2888_)) as u8;
                        if v_isSharedCheck_2908_ == 0 {
                            v___x_2900_ = v_v_2888_;
                            v_isShared_2901_ = v_isSharedCheck_2908_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2898_);
                            lean_inc(v_key_2897_);
                            lean_dec(v_v_2888_);
                            v___x_2900_ = lean_box(0);
                            v_isShared_2901_ = v_isSharedCheck_2908_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2909_ = lean_ctor_get(v_v_2888_, 0);
                        v_isSharedCheck_2919_ = (!lean_is_exclusive(v_v_2888_)) as u8;
                        if v_isSharedCheck_2919_ == 0 {
                            v___x_2911_ = v_v_2888_;
                            v_isShared_2912_ = v_isSharedCheck_2919_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2909_);
                            lean_dec(v_v_2888_);
                            v___x_2911_ = lean_box(0);
                            v_isShared_2912_ = v_isSharedCheck_2919_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2920_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2920_, 0, v_x_2875_);
                        lean_ctor_set(v___x_2920_, 1, v_x_2876_);
                        v___y_2892_ = v___x_2920_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2893_ = lean_array_fset(v_xs_x27_2890_, v_j_2882_, v___y_2892_);
                lean_dec(v_j_2882_);
                if v_isShared_2887_ == 0 {
                    lean_ctor_set(v___x_2886_, 0, v___x_2893_);
                    v___x_2895_ = v___x_2886_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2893_);
                    v___x_2895_ = v_reuseFailAlloc_2896_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2895_;
            }
            4 => {
                v___x_2902_ = l_Lean_instBEqMVarId_beq(v_x_2875_, v_key_2897_);
                if v___x_2902_ == 0 {
                    lean_del_object(v___x_2900_);
                    v___x_2903_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2897_,
                        v_val_2898_,
                        v_x_2875_,
                        v_x_2876_,
                    );
                    v___x_2904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2904_, 0, v___x_2903_);
                    v___y_2892_ = v___x_2904_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2898_);
                    lean_dec(v_key_2897_);
                    if v_isShared_2901_ == 0 {
                        lean_ctor_set(v___x_2900_, 1, v_x_2876_);
                        lean_ctor_set(v___x_2900_, 0, v_x_2875_);
                        v___x_2906_ = v___x_2900_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2907_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_x_2875_);
                        lean_ctor_set(v_reuseFailAlloc_2907_, 1, v_x_2876_);
                        v___x_2906_ = v_reuseFailAlloc_2907_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2892_ = v___x_2906_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2913_ = lean_usize_shift_right(v_x_2873_, v___x_2878_);
                v___x_2914_ = lean_usize_add(v_x_2874_, v___x_2879_);
                v___x_2915_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_node_2909_, v___x_2913_, v___x_2914_, v_x_2875_, v_x_2876_);
                if v_isShared_2912_ == 0 {
                    lean_ctor_set(v___x_2911_, 0, v___x_2915_);
                    v___x_2917_ = v___x_2911_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2918_, 0, v___x_2915_);
                    v___x_2917_ = v_reuseFailAlloc_2918_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2892_ = v___x_2917_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2927_ == 0 {
                    v___x_2929_ = v___x_2926_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_ks_2923_);
                    lean_ctor_set(v_reuseFailAlloc_2943_, 1, v_vs_2924_);
                    v___x_2929_ = v_reuseFailAlloc_2943_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2930_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v___x_2929_, v_x_2875_, v_x_2876_);
                v___x_2938_ = 7usize;
                v___x_2939_ = lean_usize_dec_le(v___x_2938_, v_x_2874_);
                if v___x_2939_ == 0 {
                    v___x_2940_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2930_);
                    v___x_2941_ = lean_unsigned_to_nat(4);
                    v___x_2942_ = lean_nat_dec_lt(v___x_2940_, v___x_2941_);
                    lean_dec(v___x_2940_);
                    v___y_2932_ = v___x_2942_;
                    state = 10;
                    continue;
                } else {
                    v___y_2932_ = v___x_2939_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2932_ == 0 {
                    v_ks_2933_ = lean_ctor_get(v_newNode_2930_, 0);
                    lean_inc_ref(v_ks_2933_);
                    v_vs_2934_ = lean_ctor_get(v_newNode_2930_, 1);
                    lean_inc_ref(v_vs_2934_);
                    lean_dec_ref(v_newNode_2930_);
                    v___x_2935_ = lean_unsigned_to_nat(0);
                    v___x_2936_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___closed__2);
                    v___x_2937_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_x_2874_, v_ks_2933_, v_vs_2934_, v___x_2935_, v___x_2936_);
                    lean_dec_ref(v_vs_2934_);
                    lean_dec_ref(v_ks_2933_);
                    return v___x_2937_;
                } else {
                    return v_newNode_2930_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(
    mut v_depth_2945_: usize,
    mut v_keys_2946_: *mut LeanObject,
    mut v_vals_2947_: *mut LeanObject,
    mut v_i_2948_: *mut LeanObject,
    mut v_entries_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: u8 = 0;
    let mut v_k_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: u64 = 0;
    let mut v_h_2955_: usize = 0;
    let mut v___x_2956_: usize = 0;
    let mut v___x_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: usize = 0;
    let mut v___x_2959_: usize = 0;
    let mut v___x_2960_: usize = 0;
    let mut v_h_2961_: usize = 0;
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2950_ = lean_array_get_size(v_keys_2946_);
                v___x_2951_ = lean_nat_dec_lt(v_i_2948_, v___x_2950_);
                if v___x_2951_ == 0 {
                    lean_dec(v_i_2948_);
                    return v_entries_2949_;
                } else {
                    v_k_2952_ = lean_array_fget_borrowed(v_keys_2946_, v_i_2948_);
                    v_v_2953_ = lean_array_fget_borrowed(v_vals_2947_, v_i_2948_);
                    v___x_2954_ = l_Lean_instHashableMVarId_hash(v_k_2952_);
                    v_h_2955_ = lean_uint64_to_usize(v___x_2954_);
                    v___x_2956_ = 5usize;
                    v___x_2957_ = lean_unsigned_to_nat(1);
                    v___x_2958_ = 1usize;
                    v___x_2959_ = lean_usize_sub(v_depth_2945_, v___x_2958_);
                    v___x_2960_ = lean_usize_mul(v___x_2956_, v___x_2959_);
                    v_h_2961_ = lean_usize_shift_right(v_h_2955_, v___x_2960_);
                    v___x_2962_ = lean_nat_add(v_i_2948_, v___x_2957_);
                    lean_dec(v_i_2948_);
                    lean_inc(v_v_2953_);
                    lean_inc(v_k_2952_);
                    v___x_2963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_entries_2949_, v_h_2961_, v_depth_2945_, v_k_2952_, v_v_2953_);
                    v_i_2948_ = v___x_2962_;
                    v_entries_2949_ = v___x_2963_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg___boxed(
    mut v_depth_2965_: *mut LeanObject,
    mut v_keys_2966_: *mut LeanObject,
    mut v_vals_2967_: *mut LeanObject,
    mut v_i_2968_: *mut LeanObject,
    mut v_entries_2969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2970_: usize = 0;
    let mut v_res_2971_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2970_ = lean_unbox_usize(v_depth_2965_);
    lean_dec(v_depth_2965_);
    v_res_2971_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_boxed_2970_, v_keys_2966_, v_vals_2967_, v_i_2968_, v_entries_2969_);
    lean_dec_ref(v_vals_2967_);
    lean_dec_ref(v_keys_2966_);
    return v_res_2971_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg___boxed(
    mut v_x_2972_: *mut LeanObject,
    mut v_x_2973_: *mut LeanObject,
    mut v_x_2974_: *mut LeanObject,
    mut v_x_2975_: *mut LeanObject,
    mut v_x_2976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_10948__boxed_2977_: usize = 0;
    let mut v_x_10949__boxed_2978_: usize = 0;
    let mut v_res_2979_: *mut LeanObject = core::ptr::null_mut();
    v_x_10948__boxed_2977_ = lean_unbox_usize(v_x_2973_);
    lean_dec(v_x_2973_);
    v_x_10949__boxed_2978_ = lean_unbox_usize(v_x_2974_);
    lean_dec(v_x_2974_);
    v_res_2979_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_2972_, v_x_10948__boxed_2977_, v_x_10949__boxed_2978_, v_x_2975_, v_x_2976_);
    return v_res_2979_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(
    mut v_x_2980_: *mut LeanObject,
    mut v_x_2981_: *mut LeanObject,
    mut v_x_2982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2983_: u64 = 0;
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: usize = 0;
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    v___x_2983_ = l_Lean_instHashableMVarId_hash(v_x_2981_);
    v___x_2984_ = lean_uint64_to_usize(v___x_2983_);
    v___x_2985_ = 1usize;
    v___x_2986_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_2980_, v___x_2984_, v___x_2985_, v_x_2981_, v_x_2982_);
    return v___x_2986_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(
    mut v_mvarId_2987_: *mut LeanObject,
    mut v_val_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2999_: u8 = 0;
    let mut v_depth_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_3001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_3008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3012_: u8 = 0;
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3023_: u8 = 0;
    let mut v_isSharedCheck_3024_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_st_ref_take(v___y_2989_);
                v_mctx_2992_ = lean_ctor_get(v___x_2991_, 0);
                v_cache_2993_ = lean_ctor_get(v___x_2991_, 1);
                v_zetaDeltaFVarIds_2994_ = lean_ctor_get(v___x_2991_, 2);
                v_postponed_2995_ = lean_ctor_get(v___x_2991_, 3);
                v_diag_2996_ = lean_ctor_get(v___x_2991_, 4);
                v_isSharedCheck_3024_ = (!lean_is_exclusive(v___x_2991_)) as u8;
                if v_isSharedCheck_3024_ == 0 {
                    v___x_2998_ = v___x_2991_;
                    v_isShared_2999_ = v_isSharedCheck_3024_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_2996_);
                    lean_inc(v_postponed_2995_);
                    lean_inc(v_zetaDeltaFVarIds_2994_);
                    lean_inc(v_cache_2993_);
                    lean_inc(v_mctx_2992_);
                    lean_dec(v___x_2991_);
                    v___x_2998_ = lean_box(0);
                    v_isShared_2999_ = v_isSharedCheck_3024_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_3000_ = lean_ctor_get(v_mctx_2992_, 0);
                v_levelAssignDepth_3001_ = lean_ctor_get(v_mctx_2992_, 1);
                v_lmvarCounter_3002_ = lean_ctor_get(v_mctx_2992_, 2);
                v_mvarCounter_3003_ = lean_ctor_get(v_mctx_2992_, 3);
                v_lDecls_3004_ = lean_ctor_get(v_mctx_2992_, 4);
                v_decls_3005_ = lean_ctor_get(v_mctx_2992_, 5);
                v_userNames_3006_ = lean_ctor_get(v_mctx_2992_, 6);
                v_lAssignment_3007_ = lean_ctor_get(v_mctx_2992_, 7);
                v_eAssignment_3008_ = lean_ctor_get(v_mctx_2992_, 8);
                v_dAssignment_3009_ = lean_ctor_get(v_mctx_2992_, 9);
                v_isSharedCheck_3023_ = (!lean_is_exclusive(v_mctx_2992_)) as u8;
                if v_isSharedCheck_3023_ == 0 {
                    v___x_3011_ = v_mctx_2992_;
                    v_isShared_3012_ = v_isSharedCheck_3023_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_3009_);
                    lean_inc(v_eAssignment_3008_);
                    lean_inc(v_lAssignment_3007_);
                    lean_inc(v_userNames_3006_);
                    lean_inc(v_decls_3005_);
                    lean_inc(v_lDecls_3004_);
                    lean_inc(v_mvarCounter_3003_);
                    lean_inc(v_lmvarCounter_3002_);
                    lean_inc(v_levelAssignDepth_3001_);
                    lean_inc(v_depth_3000_);
                    lean_dec(v_mctx_2992_);
                    v___x_3011_ = lean_box(0);
                    v_isShared_3012_ = v_isSharedCheck_3023_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3013_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_eAssignment_3008_, v_mvarId_2987_, v_val_2988_);
                if v_isShared_3012_ == 0 {
                    lean_ctor_set(v___x_3011_, 8, v___x_3013_);
                    v___x_3015_ = v___x_3011_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_depth_3000_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 1, v_levelAssignDepth_3001_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 2, v_lmvarCounter_3002_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 3, v_mvarCounter_3003_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 4, v_lDecls_3004_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 5, v_decls_3005_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 6, v_userNames_3006_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 7, v_lAssignment_3007_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 8, v___x_3013_);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 9, v_dAssignment_3009_);
                    v___x_3015_ = v_reuseFailAlloc_3022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2999_ == 0 {
                    lean_ctor_set(v___x_2998_, 0, v___x_3015_);
                    v___x_3017_ = v___x_2998_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3021_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3015_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 1, v_cache_2993_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 2, v_zetaDeltaFVarIds_2994_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 3, v_postponed_2995_);
                    lean_ctor_set(v_reuseFailAlloc_3021_, 4, v_diag_2996_);
                    v___x_3017_ = v_reuseFailAlloc_3021_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3018_ = lean_st_ref_set(v___y_2989_, v___x_3017_);
                v___x_3019_ = lean_box(0);
                v___x_3020_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3020_, 0, v___x_3019_);
                return v___x_3020_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg___boxed(
    mut v_mvarId_3025_: *mut LeanObject,
    mut v_val_3026_: *mut LeanObject,
    mut v___y_3027_: *mut LeanObject,
    mut v___y_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3029_: *mut LeanObject = core::ptr::null_mut();
    v_res_3029_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(
            v_mvarId_3025_,
            v_val_3026_,
            v___y_3027_,
        );
    lean_dec(v___y_3027_);
    return v_res_3029_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(
    mut v_msg_3030_: *mut LeanObject,
    mut v___y_3031_: *mut LeanObject,
    mut v___y_3032_: *mut LeanObject,
    mut v___y_3033_: *mut LeanObject,
    mut v___y_3034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_3036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3041_: u8 = 0;
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_3036_ = lean_ctor_get(v___y_3033_, 5);
                v___x_3037_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0_spec__0(v_msg_3030_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
                v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
                v_isSharedCheck_3046_ = (!lean_is_exclusive(v___x_3037_)) as u8;
                if v_isSharedCheck_3046_ == 0 {
                    v___x_3040_ = v___x_3037_;
                    v_isShared_3041_ = v_isSharedCheck_3046_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_3038_);
                    lean_dec(v___x_3037_);
                    v___x_3040_ = lean_box(0);
                    v_isShared_3041_ = v_isSharedCheck_3046_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_3036_);
                v___x_3042_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3042_, 0, v_ref_3036_);
                lean_ctor_set(v___x_3042_, 1, v_a_3038_);
                if v_isShared_3041_ == 0 {
                    lean_ctor_set_tag(v___x_3040_, 1);
                    lean_ctor_set(v___x_3040_, 0, v___x_3042_);
                    v___x_3044_ = v___x_3040_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3042_);
                    v___x_3044_ = v_reuseFailAlloc_3045_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg___boxed(
    mut v_msg_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
    mut v___y_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3053_: *mut LeanObject = core::ptr::null_mut();
    v_res_3053_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(
            v_msg_3047_,
            v___y_3048_,
            v___y_3049_,
            v___y_3050_,
            v___y_3051_,
        );
    lean_dec(v___y_3051_);
    lean_dec_ref(v___y_3050_);
    lean_dec(v___y_3049_);
    lean_dec_ref(v___y_3048_);
    return v_res_3053_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(
    mut v_k_3054_: *mut LeanObject,
    mut v___y_3055_: *mut LeanObject,
    mut v___y_3056_: *mut LeanObject,
    mut v___y_3057_: *mut LeanObject,
    mut v___y_3058_: *mut LeanObject,
    mut v_b_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
    mut v___y_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_3063_);
    lean_inc_ref(v___y_3062_);
    lean_inc(v___y_3061_);
    lean_inc_ref(v___y_3060_);
    lean_inc(v___y_3058_);
    lean_inc_ref(v___y_3057_);
    lean_inc(v___y_3056_);
    lean_inc_ref(v___y_3055_);
    v___x_3065_ = lean_apply_10(
        v_k_3054_,
        v_b_3059_,
        v___y_3055_,
        v___y_3056_,
        v___y_3057_,
        v___y_3058_,
        v___y_3060_,
        v___y_3061_,
        v___y_3062_,
        v___y_3063_,
        lean_box(0),
    );
    return v___x_3065_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed(
    mut v_k_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
    mut v___y_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
    mut v_b_3071_: *mut LeanObject,
    mut v___y_3072_: *mut LeanObject,
    mut v___y_3073_: *mut LeanObject,
    mut v___y_3074_: *mut LeanObject,
    mut v___y_3075_: *mut LeanObject,
    mut v___y_3076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3077_: *mut LeanObject = core::ptr::null_mut();
    v_res_3077_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0(v_k_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_, v_b_3071_, v___y_3072_, v___y_3073_, v___y_3074_, v___y_3075_);
    lean_dec(v___y_3075_);
    lean_dec_ref(v___y_3074_);
    lean_dec(v___y_3073_);
    lean_dec_ref(v___y_3072_);
    lean_dec(v___y_3070_);
    lean_dec_ref(v___y_3069_);
    lean_dec(v___y_3068_);
    lean_dec_ref(v___y_3067_);
    return v_res_3077_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(
    mut v_name_3078_: *mut LeanObject,
    mut v_bi_3079_: u8,
    mut v_type_3080_: *mut LeanObject,
    mut v_k_3081_: *mut LeanObject,
    mut v_kind_3082_: u8,
    mut v___y_3083_: *mut LeanObject,
    mut v___y_3084_: *mut LeanObject,
    mut v___y_3085_: *mut LeanObject,
    mut v___y_3086_: *mut LeanObject,
    mut v___y_3087_: *mut LeanObject,
    mut v___y_3088_: *mut LeanObject,
    mut v___y_3089_: *mut LeanObject,
    mut v___y_3090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3097_: u8 = 0;
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3086_);
                lean_inc_ref(v___y_3085_);
                lean_inc(v___y_3084_);
                lean_inc_ref(v___y_3083_);
                v___f_3092_ = lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                lean_closure_set(v___f_3092_, 0, v_k_3081_);
                lean_closure_set(v___f_3092_, 1, v___y_3083_);
                lean_closure_set(v___f_3092_, 2, v___y_3084_);
                lean_closure_set(v___f_3092_, 3, v___y_3085_);
                lean_closure_set(v___f_3092_, 4, v___y_3086_);
                v___x_3093_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    lean_box(0),
                    v_name_3078_,
                    v_bi_3079_,
                    v_type_3080_,
                    v___f_3092_,
                    v_kind_3082_,
                    v___y_3087_,
                    v___y_3088_,
                    v___y_3089_,
                    v___y_3090_,
                );
                if lean_obj_tag(v___x_3093_) == 0 {
                    return v___x_3093_;
                } else {
                    v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
                    v_isSharedCheck_3101_ = (!lean_is_exclusive(v___x_3093_)) as u8;
                    if v_isSharedCheck_3101_ == 0 {
                        v___x_3096_ = v___x_3093_;
                        v_isShared_3097_ = v_isSharedCheck_3101_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3094_);
                        lean_dec(v___x_3093_);
                        v___x_3096_ = lean_box(0);
                        v_isShared_3097_ = v_isSharedCheck_3101_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3097_ == 0 {
                    v___x_3099_ = v___x_3096_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
                    v___x_3099_ = v_reuseFailAlloc_3100_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg___boxed(
    mut v_name_3102_: *mut LeanObject,
    mut v_bi_3103_: *mut LeanObject,
    mut v_type_3104_: *mut LeanObject,
    mut v_k_3105_: *mut LeanObject,
    mut v_kind_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
    mut v___y_3115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3116_: u8 = 0;
    let mut v_kind_boxed_3117_: u8 = 0;
    let mut v_res_3118_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3116_ = (lean_unbox(v_bi_3103_) as u8);
    v_kind_boxed_3117_ = (lean_unbox(v_kind_3106_) as u8);
    v_res_3118_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_3102_, v_bi_boxed_3116_, v_type_3104_, v_k_3105_, v_kind_boxed_3117_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
    lean_dec(v___y_3114_);
    lean_dec_ref(v___y_3113_);
    lean_dec(v___y_3112_);
    lean_dec_ref(v___y_3111_);
    lean_dec(v___y_3110_);
    lean_dec_ref(v___y_3109_);
    lean_dec(v___y_3108_);
    lean_dec_ref(v___y_3107_);
    return v_res_3118_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(
    mut v_name_3119_: *mut LeanObject,
    mut v_type_3120_: *mut LeanObject,
    mut v_k_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
    mut v___y_3127_: *mut LeanObject,
    mut v___y_3128_: *mut LeanObject,
    mut v___y_3129_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3131_: u8 = 0;
    let mut v___x_3132_: u8 = 0;
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    v___x_3131_ = 0;
    v___x_3132_ = 0;
    v___x_3133_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_3119_, v___x_3131_, v_type_3120_, v_k_3121_, v___x_3132_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
    return v___x_3133_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg___boxed(
    mut v_name_3134_: *mut LeanObject,
    mut v_type_3135_: *mut LeanObject,
    mut v_k_3136_: *mut LeanObject,
    mut v___y_3137_: *mut LeanObject,
    mut v___y_3138_: *mut LeanObject,
    mut v___y_3139_: *mut LeanObject,
    mut v___y_3140_: *mut LeanObject,
    mut v___y_3141_: *mut LeanObject,
    mut v___y_3142_: *mut LeanObject,
    mut v___y_3143_: *mut LeanObject,
    mut v___y_3144_: *mut LeanObject,
    mut v___y_3145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3146_: *mut LeanObject = core::ptr::null_mut();
    v_res_3146_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_3134_, v_type_3135_, v_k_3136_, v___y_3137_, v___y_3138_, v___y_3139_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, v___y_3144_);
    lean_dec(v___y_3144_);
    lean_dec_ref(v___y_3143_);
    lean_dec(v___y_3142_);
    lean_dec_ref(v___y_3141_);
    lean_dec(v___y_3140_);
    lean_dec_ref(v___y_3139_);
    lean_dec(v___y_3138_);
    lean_dec_ref(v___y_3137_);
    return v_res_3146_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(
    mut v_kSuccess_3147_: *mut LeanObject,
    mut v_a_3148_: *mut LeanObject,
    mut v_goal_3149_: *mut LeanObject,
    mut v_a_3150_: u8,
    mut v___x_3151_: u8,
    mut v___x_3152_: *mut LeanObject,
    mut v___x_3153_: *mut LeanObject,
    mut v___x_3154_: *mut LeanObject,
    mut v___x_3155_: *mut LeanObject,
    mut v___x_3156_: *mut LeanObject,
    mut v_00_u03c3s_3157_: *mut LeanObject,
    mut v_hyps_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_target_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_h_u03c6_3162_: *mut LeanObject,
    mut v___y_3163_: *mut LeanObject,
    mut v___y_3164_: *mut LeanObject,
    mut v___y_3165_: *mut LeanObject,
    mut v___y_3166_: *mut LeanObject,
    mut v___y_3167_: *mut LeanObject,
    mut v___y_3168_: *mut LeanObject,
    mut v___y_3169_: *mut LeanObject,
    mut v___y_3170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: u8 = 0;
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3182_: u8 = 0;
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_prf_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_3170_);
                lean_inc_ref(v___y_3169_);
                lean_inc(v___y_3168_);
                lean_inc_ref(v___y_3167_);
                lean_inc(v___y_3166_);
                lean_inc_ref(v___y_3165_);
                lean_inc(v___y_3164_);
                lean_inc_ref(v___y_3163_);
                lean_inc_ref(v_h_u03c6_3162_);
                lean_inc_ref(v_a_3148_);
                v___x_3172_ = lean_apply_12(
                    v_kSuccess_3147_,
                    v_a_3148_,
                    v_h_u03c6_3162_,
                    v_goal_3149_,
                    v___y_3163_,
                    v___y_3164_,
                    v___y_3165_,
                    v___y_3166_,
                    v___y_3167_,
                    v___y_3168_,
                    v___y_3169_,
                    v___y_3170_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3172_) == 0 {
                    v_a_3173_ = lean_ctor_get(v___x_3172_, 0);
                    lean_inc(v_a_3173_);
                    lean_dec_ref_known(v___x_3172_, 1);
                    v___x_3174_ = lean_unsigned_to_nat(1);
                    v___x_3175_ = lean_mk_empty_array_with_capacity(v___x_3174_);
                    v___x_3176_ = lean_array_push(v___x_3175_, v_h_u03c6_3162_);
                    v___x_3177_ = 1;
                    v___x_3178_ = l_Lean_Meta_mkLambdaFVars(
                        v___x_3176_,
                        v_a_3173_,
                        v_a_3150_,
                        v___x_3151_,
                        v_a_3150_,
                        v___x_3151_,
                        v___x_3177_,
                        v___y_3167_,
                        v___y_3168_,
                        v___y_3169_,
                        v___y_3170_,
                    );
                    lean_dec_ref(v___x_3176_);
                    if lean_obj_tag(v___x_3178_) == 0 {
                        v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
                        v_isSharedCheck_3191_ = (!lean_is_exclusive(v___x_3178_)) as u8;
                        if v_isSharedCheck_3191_ == 0 {
                            v___x_3181_ = v___x_3178_;
                            v_isShared_3182_ = v_isSharedCheck_3191_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3179_);
                            lean_dec(v___x_3178_);
                            v___x_3181_ = lean_box(0);
                            v_isShared_3182_ = v_isSharedCheck_3191_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_a_3161_);
                        lean_dec_ref(v_target_3160_);
                        lean_dec_ref(v_a_3159_);
                        lean_dec_ref(v_hyps_3158_);
                        lean_dec_ref(v_00_u03c3s_3157_);
                        lean_dec(v___x_3156_);
                        lean_dec_ref(v___x_3155_);
                        lean_dec_ref(v___x_3154_);
                        lean_dec_ref(v___x_3153_);
                        lean_dec_ref(v___x_3152_);
                        lean_dec_ref(v_a_3148_);
                        return v___x_3178_;
                    }
                } else {
                    lean_dec_ref(v_h_u03c6_3162_);
                    lean_dec_ref(v_a_3161_);
                    lean_dec_ref(v_target_3160_);
                    lean_dec_ref(v_a_3159_);
                    lean_dec_ref(v_hyps_3158_);
                    lean_dec_ref(v_00_u03c3s_3157_);
                    lean_dec(v___x_3156_);
                    lean_dec_ref(v___x_3155_);
                    lean_dec_ref(v___x_3154_);
                    lean_dec_ref(v___x_3153_);
                    lean_dec_ref(v___x_3152_);
                    lean_dec_ref(v_a_3148_);
                    return v___x_3172_;
                }
            }
            1 => {
                v___x_3183_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__0;
                v___x_3184_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__0___closed__1;
                v___x_3185_ = l_Lean_Name_mkStr6(
                    v___x_3152_,
                    v___x_3153_,
                    v___x_3154_,
                    v___x_3155_,
                    v___x_3183_,
                    v___x_3184_,
                );
                v___x_3186_ = l_Lean_mkConst(v___x_3185_, v___x_3156_);
                v_prf_3187_ = l_Lean_mkApp7(
                    v___x_3186_,
                    v_00_u03c3s_3157_,
                    v_hyps_3158_,
                    v_a_3159_,
                    v_target_3160_,
                    v_a_3148_,
                    v_a_3161_,
                    v_a_3179_,
                );
                if v_isShared_3182_ == 0 {
                    lean_ctor_set(v___x_3181_, 0, v_prf_3187_);
                    v___x_3189_ = v___x_3181_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3190_, 0, v_prf_3187_);
                    v___x_3189_ = v_reuseFailAlloc_3190_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_kSuccess_3192_: *mut LeanObject = *_args.add(0);
    let mut v_a_3193_: *mut LeanObject = *_args.add(1);
    let mut v_goal_3194_: *mut LeanObject = *_args.add(2);
    let mut v_a_3195_: *mut LeanObject = *_args.add(3);
    let mut v___x_3196_: *mut LeanObject = *_args.add(4);
    let mut v___x_3197_: *mut LeanObject = *_args.add(5);
    let mut v___x_3198_: *mut LeanObject = *_args.add(6);
    let mut v___x_3199_: *mut LeanObject = *_args.add(7);
    let mut v___x_3200_: *mut LeanObject = *_args.add(8);
    let mut v___x_3201_: *mut LeanObject = *_args.add(9);
    let mut v_00_u03c3s_3202_: *mut LeanObject = *_args.add(10);
    let mut v_hyps_3203_: *mut LeanObject = *_args.add(11);
    let mut v_a_3204_: *mut LeanObject = *_args.add(12);
    let mut v_target_3205_: *mut LeanObject = *_args.add(13);
    let mut v_a_3206_: *mut LeanObject = *_args.add(14);
    let mut v_h_u03c6_3207_: *mut LeanObject = *_args.add(15);
    let mut v___y_3208_: *mut LeanObject = *_args.add(16);
    let mut v___y_3209_: *mut LeanObject = *_args.add(17);
    let mut v___y_3210_: *mut LeanObject = *_args.add(18);
    let mut v___y_3211_: *mut LeanObject = *_args.add(19);
    let mut v___y_3212_: *mut LeanObject = *_args.add(20);
    let mut v___y_3213_: *mut LeanObject = *_args.add(21);
    let mut v___y_3214_: *mut LeanObject = *_args.add(22);
    let mut v___y_3215_: *mut LeanObject = *_args.add(23);
    let mut v___y_3216_: *mut LeanObject = *_args.add(24);
    let mut v_a_11316__boxed_3217_: u8 = 0;
    let mut v___x_11317__boxed_3218_: u8 = 0;
    let mut v_res_3219_: *mut LeanObject = core::ptr::null_mut();
    v_a_11316__boxed_3217_ = (lean_unbox(v_a_3195_) as u8);
    v___x_11317__boxed_3218_ = (lean_unbox(v___x_3196_) as u8);
    v_res_3219_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0(v_kSuccess_3192_, v_a_3193_, v_goal_3194_, v_a_11316__boxed_3217_, v___x_11317__boxed_3218_, v___x_3197_, v___x_3198_, v___x_3199_, v___x_3200_, v___x_3201_, v_00_u03c3s_3202_, v_hyps_3203_, v_a_3204_, v_target_3205_, v_a_3206_, v_h_u03c6_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_, v___y_3215_);
    lean_dec(v___y_3215_);
    lean_dec_ref(v___y_3214_);
    lean_dec(v___y_3213_);
    lean_dec_ref(v___y_3212_);
    lean_dec(v___y_3211_);
    lean_dec_ref(v___y_3210_);
    lean_dec(v___y_3209_);
    lean_dec_ref(v___y_3208_);
    return v_res_3219_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: *mut LeanObject = core::ptr::null_mut();
    v___x_3226_ = lean_box(0);
    v___x_3227_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__7___closed__1;
    v___x_3228_ = l_Lean_mkConst(v___x_3227_, v___x_3226_);
    return v___x_3228_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(
    mut v_goal_3229_: *mut LeanObject,
    mut v_kFail_3230_: *mut LeanObject,
    mut v_kSuccess_3231_: *mut LeanObject,
    mut v___y_3232_: *mut LeanObject,
    mut v___y_3233_: *mut LeanObject,
    mut v___y_3234_: *mut LeanObject,
    mut v___y_3235_: *mut LeanObject,
    mut v___y_3236_: *mut LeanObject,
    mut v___y_3237_: *mut LeanObject,
    mut v___y_3238_: *mut LeanObject,
    mut v___y_3239_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_u_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_00_u03c3s_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hyps_3243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3247_: u8 = 0;
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: u8 = 0;
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3255_: u8 = 0;
    let mut v___x_3256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3279_: u8 = 0;
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: u8 = 0;
    let mut v_goal_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3295_: u8 = 0;
    let mut v___x_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3299_: u8 = 0;
    let mut v___x_3300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3304_: u8 = 0;
    let mut v___x_3306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3308_: u8 = 0;
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3313_: u8 = 0;
    let mut v___x_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3317_: u8 = 0;
    let mut v_reuseFailAlloc_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3319_: u8 = 0;
    let mut v_isSharedCheck_3320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_u_3241_ = lean_ctor_get(v_goal_3229_, 0);
                v_00_u03c3s_3242_ = lean_ctor_get(v_goal_3229_, 1);
                v_hyps_3243_ = lean_ctor_get(v_goal_3229_, 2);
                v_target_3244_ = lean_ctor_get(v_goal_3229_, 3);
                v_isSharedCheck_3320_ = (!lean_is_exclusive(v_goal_3229_)) as u8;
                if v_isSharedCheck_3320_ == 0 {
                    v___x_3246_ = v_goal_3229_;
                    v_isShared_3247_ = v_isSharedCheck_3320_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_target_3244_);
                    lean_inc(v_hyps_3243_);
                    lean_inc(v_00_u03c3s_3242_);
                    lean_inc(v_u_3241_);
                    lean_dec(v_goal_3229_);
                    v___x_3246_ = lean_box(0);
                    v_isShared_3247_ = v_isSharedCheck_3320_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3248_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___closed__1,
                );
                v___x_3249_ = 0;
                v___x_3250_ = lean_box(0);
                v___x_3251_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_3248_,
                    v___x_3249_,
                    v___x_3250_,
                    v___y_3236_,
                    v___y_3237_,
                    v___y_3238_,
                    v___y_3239_,
                );
                if lean_obj_tag(v___x_3251_) == 0 {
                    v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
                    v_isSharedCheck_3319_ = (!lean_is_exclusive(v___x_3251_)) as u8;
                    if v_isSharedCheck_3319_ == 0 {
                        v___x_3254_ = v___x_3251_;
                        v_isShared_3255_ = v_isSharedCheck_3319_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_3252_);
                        lean_dec(v___x_3251_);
                        v___x_3254_ = lean_box(0);
                        v_isShared_3255_ = v_isSharedCheck_3319_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3246_);
                    lean_dec_ref(v_target_3244_);
                    lean_dec_ref(v_hyps_3243_);
                    lean_dec_ref(v_00_u03c3s_3242_);
                    lean_dec(v_u_3241_);
                    lean_dec_ref(v_kSuccess_3231_);
                    lean_dec_ref(v_kFail_3230_);
                    return v___x_3251_;
                }
            }
            2 => {
                v___x_3256_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__0;
                v___x_3257_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__1;
                v___x_3258_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__2;
                v___x_3259_ =
                    l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__9___closed__3;
                v___x_3260_ = lean_box(0);
                lean_inc(v_u_3241_);
                v___x_3261_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3261_, 0, v_u_3241_);
                lean_ctor_set(v___x_3261_, 1, v___x_3260_);
                lean_inc_ref(v___x_3261_);
                v___x_3262_ = l_Lean_mkConst(v___x_3259_, v___x_3261_);
                lean_inc_ref(v_00_u03c3s_3242_);
                v___x_3263_ = l_Lean_Expr_app___override(v___x_3262_, v_00_u03c3s_3242_);
                if v_isShared_3255_ == 0 {
                    lean_ctor_set_tag(v___x_3254_, 1);
                    lean_ctor_set(v___x_3254_, 0, v___x_3263_);
                    v___x_3265_ = v___x_3254_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3318_, 0, v___x_3263_);
                    v___x_3265_ = v_reuseFailAlloc_3318_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3266_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_3265_,
                    v___x_3249_,
                    v___x_3250_,
                    v___y_3236_,
                    v___y_3237_,
                    v___y_3238_,
                    v___y_3239_,
                );
                if lean_obj_tag(v___x_3266_) == 0 {
                    v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
                    lean_inc_n(v_a_3267_, 2);
                    lean_dec_ref_known(v___x_3266_, 1);
                    v___x_3268_ =
                        l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___redArg___lam__8___closed__0;
                    v___x_3269_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__0;
                    lean_inc_ref(v___x_3261_);
                    v___x_3270_ = l_Lean_mkConst(v___x_3269_, v___x_3261_);
                    lean_inc(v_a_3252_);
                    lean_inc_ref(v_hyps_3243_);
                    lean_inc_ref(v_00_u03c3s_3242_);
                    v___x_3271_ = l_Lean_mkApp4(
                        v___x_3270_,
                        v_00_u03c3s_3242_,
                        v_hyps_3243_,
                        v_a_3267_,
                        v_a_3252_,
                    );
                    v___x_3272_ = lean_box(0);
                    v___x_3273_ = l_Lean_Meta_trySynthInstance(
                        v___x_3271_,
                        v___x_3272_,
                        v___y_3236_,
                        v___y_3237_,
                        v___y_3238_,
                        v___y_3239_,
                    );
                    if lean_obj_tag(v___x_3273_) == 0 {
                        v_a_3274_ = lean_ctor_get(v___x_3273_, 0);
                        lean_inc(v_a_3274_);
                        lean_dec_ref_known(v___x_3273_, 1);
                        if lean_obj_tag(v_a_3274_) == 1 {
                            v_a_3275_ = lean_ctor_get(v_a_3274_, 0);
                            lean_inc(v_a_3275_);
                            lean_dec_ref_known(v_a_3274_, 1);
                            v___x_3276_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___closed__1);
                            lean_inc(v_a_3252_);
                            v___x_3277_ = l_Lean_Meta_isExprDefEq(
                                v___x_3276_,
                                v_a_3252_,
                                v___y_3236_,
                                v___y_3237_,
                                v___y_3238_,
                                v___y_3239_,
                            );
                            if lean_obj_tag(v___x_3277_) == 0 {
                                v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
                                lean_inc(v_a_3278_);
                                lean_dec_ref_known(v___x_3277_, 1);
                                v___x_3279_ = (lean_unbox(v_a_3278_) as u8);
                                if v___x_3279_ == 0 {
                                    lean_dec_ref(v_kFail_3230_);
                                    lean_inc_ref(v_hyps_3243_);
                                    v___x_3280_ = l_Lean_Elab_Tactic_Do_ProofMode_transferHypNames(
                                        v_hyps_3243_,
                                        v_a_3267_,
                                        v___y_3236_,
                                        v___y_3237_,
                                        v___y_3238_,
                                        v___y_3239_,
                                    );
                                    if lean_obj_tag(v___x_3280_) == 0 {
                                        v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
                                        lean_inc(v_a_3281_);
                                        lean_dec_ref_known(v___x_3280_, 1);
                                        v___x_3282_ = l___private_Init_While_0__whileM_erased___at___00__private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_transferHypNames_label_spec__1___redArg___closed__1;
                                        v___x_3283_ = l_Lean_Core_mkFreshUserName(
                                            v___x_3282_,
                                            v___y_3238_,
                                            v___y_3239_,
                                        );
                                        if lean_obj_tag(v___x_3283_) == 0 {
                                            v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
                                            lean_inc(v_a_3284_);
                                            lean_dec_ref_known(v___x_3283_, 1);
                                            v___x_3285_ = 1;
                                            lean_inc_ref(v_target_3244_);
                                            lean_inc(v_a_3281_);
                                            lean_inc_ref(v_00_u03c3s_3242_);
                                            if v_isShared_3247_ == 0 {
                                                lean_ctor_set(v___x_3246_, 2, v_a_3281_);
                                                v_goal_3287_ = v___x_3246_;
                                                state = 4;
                                                continue;
                                            } else {
                                                v_reuseFailAlloc_3291_ =
                                                    lean_alloc_ctor(0, 4, (0) as u32);
                                                lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_u_3241_);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_3291_,
                                                    1,
                                                    v_00_u03c3s_3242_,
                                                );
                                                lean_ctor_set(v_reuseFailAlloc_3291_, 2, v_a_3281_);
                                                lean_ctor_set(
                                                    v_reuseFailAlloc_3291_,
                                                    3,
                                                    v_target_3244_,
                                                );
                                                v_goal_3287_ = v_reuseFailAlloc_3291_;
                                                state = 4;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_3281_);
                                            lean_dec(v_a_3278_);
                                            lean_dec(v_a_3275_);
                                            lean_dec_ref_known(v___x_3261_, 2);
                                            lean_dec(v_a_3252_);
                                            lean_del_object(v___x_3246_);
                                            lean_dec_ref(v_target_3244_);
                                            lean_dec_ref(v_hyps_3243_);
                                            lean_dec_ref(v_00_u03c3s_3242_);
                                            lean_dec(v_u_3241_);
                                            lean_dec_ref(v_kSuccess_3231_);
                                            v_a_3292_ = lean_ctor_get(v___x_3283_, 0);
                                            v_isSharedCheck_3299_ =
                                                (!lean_is_exclusive(v___x_3283_)) as u8;
                                            if v_isSharedCheck_3299_ == 0 {
                                                v___x_3294_ = v___x_3283_;
                                                v_isShared_3295_ = v_isSharedCheck_3299_;
                                                state = 5;
                                                continue;
                                            } else {
                                                lean_inc(v_a_3292_);
                                                lean_dec(v___x_3283_);
                                                v___x_3294_ = lean_box(0);
                                                v_isShared_3295_ = v_isSharedCheck_3299_;
                                                state = 5;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_3278_);
                                        lean_dec(v_a_3275_);
                                        lean_dec_ref_known(v___x_3261_, 2);
                                        lean_dec(v_a_3252_);
                                        lean_del_object(v___x_3246_);
                                        lean_dec_ref(v_target_3244_);
                                        lean_dec_ref(v_hyps_3243_);
                                        lean_dec_ref(v_00_u03c3s_3242_);
                                        lean_dec(v_u_3241_);
                                        lean_dec_ref(v_kSuccess_3231_);
                                        return v___x_3280_;
                                    }
                                } else {
                                    lean_dec(v_a_3278_);
                                    lean_dec(v_a_3275_);
                                    lean_dec(v_a_3267_);
                                    lean_dec_ref_known(v___x_3261_, 2);
                                    lean_dec(v_a_3252_);
                                    lean_del_object(v___x_3246_);
                                    lean_dec_ref(v_target_3244_);
                                    lean_dec_ref(v_hyps_3243_);
                                    lean_dec_ref(v_00_u03c3s_3242_);
                                    lean_dec(v_u_3241_);
                                    lean_dec_ref(v_kSuccess_3231_);
                                    lean_inc(v___y_3239_);
                                    lean_inc_ref(v___y_3238_);
                                    lean_inc(v___y_3237_);
                                    lean_inc_ref(v___y_3236_);
                                    lean_inc(v___y_3235_);
                                    lean_inc_ref(v___y_3234_);
                                    lean_inc(v___y_3233_);
                                    lean_inc_ref(v___y_3232_);
                                    v___x_3300_ = lean_apply_9(
                                        v_kFail_3230_,
                                        v___y_3232_,
                                        v___y_3233_,
                                        v___y_3234_,
                                        v___y_3235_,
                                        v___y_3236_,
                                        v___y_3237_,
                                        v___y_3238_,
                                        v___y_3239_,
                                        lean_box(0),
                                    );
                                    return v___x_3300_;
                                }
                            } else {
                                lean_dec(v_a_3275_);
                                lean_dec(v_a_3267_);
                                lean_dec_ref_known(v___x_3261_, 2);
                                lean_dec(v_a_3252_);
                                lean_del_object(v___x_3246_);
                                lean_dec_ref(v_target_3244_);
                                lean_dec_ref(v_hyps_3243_);
                                lean_dec_ref(v_00_u03c3s_3242_);
                                lean_dec(v_u_3241_);
                                lean_dec_ref(v_kSuccess_3231_);
                                lean_dec_ref(v_kFail_3230_);
                                v_a_3301_ = lean_ctor_get(v___x_3277_, 0);
                                v_isSharedCheck_3308_ = (!lean_is_exclusive(v___x_3277_)) as u8;
                                if v_isSharedCheck_3308_ == 0 {
                                    v___x_3303_ = v___x_3277_;
                                    v_isShared_3304_ = v_isSharedCheck_3308_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3301_);
                                    lean_dec(v___x_3277_);
                                    v___x_3303_ = lean_box(0);
                                    v_isShared_3304_ = v_isSharedCheck_3308_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_3274_);
                            lean_dec(v_a_3267_);
                            lean_dec_ref_known(v___x_3261_, 2);
                            lean_dec(v_a_3252_);
                            lean_del_object(v___x_3246_);
                            lean_dec_ref(v_target_3244_);
                            lean_dec_ref(v_hyps_3243_);
                            lean_dec_ref(v_00_u03c3s_3242_);
                            lean_dec(v_u_3241_);
                            lean_dec_ref(v_kSuccess_3231_);
                            lean_inc(v___y_3239_);
                            lean_inc_ref(v___y_3238_);
                            lean_inc(v___y_3237_);
                            lean_inc_ref(v___y_3236_);
                            lean_inc(v___y_3235_);
                            lean_inc_ref(v___y_3234_);
                            lean_inc(v___y_3233_);
                            lean_inc_ref(v___y_3232_);
                            v___x_3309_ = lean_apply_9(
                                v_kFail_3230_,
                                v___y_3232_,
                                v___y_3233_,
                                v___y_3234_,
                                v___y_3235_,
                                v___y_3236_,
                                v___y_3237_,
                                v___y_3238_,
                                v___y_3239_,
                                lean_box(0),
                            );
                            return v___x_3309_;
                        }
                    } else {
                        lean_dec(v_a_3267_);
                        lean_dec_ref_known(v___x_3261_, 2);
                        lean_dec(v_a_3252_);
                        lean_del_object(v___x_3246_);
                        lean_dec_ref(v_target_3244_);
                        lean_dec_ref(v_hyps_3243_);
                        lean_dec_ref(v_00_u03c3s_3242_);
                        lean_dec(v_u_3241_);
                        lean_dec_ref(v_kSuccess_3231_);
                        lean_dec_ref(v_kFail_3230_);
                        v_a_3310_ = lean_ctor_get(v___x_3273_, 0);
                        v_isSharedCheck_3317_ = (!lean_is_exclusive(v___x_3273_)) as u8;
                        if v_isSharedCheck_3317_ == 0 {
                            v___x_3312_ = v___x_3273_;
                            v_isShared_3313_ = v_isSharedCheck_3317_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3310_);
                            lean_dec(v___x_3273_);
                            v___x_3312_ = lean_box(0);
                            v_isShared_3313_ = v_isSharedCheck_3317_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref_known(v___x_3261_, 2);
                    lean_dec(v_a_3252_);
                    lean_del_object(v___x_3246_);
                    lean_dec_ref(v_target_3244_);
                    lean_dec_ref(v_hyps_3243_);
                    lean_dec_ref(v_00_u03c3s_3242_);
                    lean_dec(v_u_3241_);
                    lean_dec_ref(v_kSuccess_3231_);
                    lean_dec_ref(v_kFail_3230_);
                    return v___x_3266_;
                }
            }
            4 => {
                v___x_3288_ = lean_box((v___x_3285_) as usize);
                lean_inc(v_a_3252_);
                v___f_3289_ = lean_alloc_closure(l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___lam__0___boxed as *mut core::ffi::c_void, 25, 15);
                lean_closure_set(v___f_3289_, 0, v_kSuccess_3231_);
                lean_closure_set(v___f_3289_, 1, v_a_3252_);
                lean_closure_set(v___f_3289_, 2, v_goal_3287_);
                lean_closure_set(v___f_3289_, 3, v_a_3278_);
                lean_closure_set(v___f_3289_, 4, v___x_3288_);
                lean_closure_set(v___f_3289_, 5, v___x_3256_);
                lean_closure_set(v___f_3289_, 6, v___x_3257_);
                lean_closure_set(v___f_3289_, 7, v___x_3258_);
                lean_closure_set(v___f_3289_, 8, v___x_3268_);
                lean_closure_set(v___f_3289_, 9, v___x_3261_);
                lean_closure_set(v___f_3289_, 10, v_00_u03c3s_3242_);
                lean_closure_set(v___f_3289_, 11, v_hyps_3243_);
                lean_closure_set(v___f_3289_, 12, v_a_3281_);
                lean_closure_set(v___f_3289_, 13, v_target_3244_);
                lean_closure_set(v___f_3289_, 14, v_a_3275_);
                v___x_3290_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_a_3284_, v_a_3252_, v___f_3289_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_, v___y_3237_, v___y_3238_, v___y_3239_);
                return v___x_3290_;
            }
            5 => {
                if v_isShared_3295_ == 0 {
                    v___x_3297_ = v___x_3294_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3298_, 0, v_a_3292_);
                    v___x_3297_ = v_reuseFailAlloc_3298_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3297_;
            }
            7 => {
                if v_isShared_3304_ == 0 {
                    v___x_3306_ = v___x_3303_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
                    v___x_3306_ = v_reuseFailAlloc_3307_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3306_;
            }
            9 => {
                if v_isShared_3313_ == 0 {
                    v___x_3315_ = v___x_3312_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3316_, 0, v_a_3310_);
                    v___x_3315_ = v_reuseFailAlloc_3316_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3315_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2___boxed(
    mut v_goal_3321_: *mut LeanObject,
    mut v_kFail_3322_: *mut LeanObject,
    mut v_kSuccess_3323_: *mut LeanObject,
    mut v___y_3324_: *mut LeanObject,
    mut v___y_3325_: *mut LeanObject,
    mut v___y_3326_: *mut LeanObject,
    mut v___y_3327_: *mut LeanObject,
    mut v___y_3328_: *mut LeanObject,
    mut v___y_3329_: *mut LeanObject,
    mut v___y_3330_: *mut LeanObject,
    mut v___y_3331_: *mut LeanObject,
    mut v___y_3332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3333_: *mut LeanObject = core::ptr::null_mut();
    v_res_3333_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_goal_3321_, v_kFail_3322_, v_kSuccess_3323_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
    lean_dec(v___y_3331_);
    lean_dec_ref(v___y_3330_);
    lean_dec(v___y_3329_);
    lean_dec_ref(v___y_3328_);
    lean_dec(v___y_3327_);
    lean_dec_ref(v___y_3326_);
    lean_dec(v___y_3325_);
    lean_dec_ref(v___y_3324_);
    return v_res_3333_;
}
pub unsafe fn _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1()
-> *mut LeanObject {
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    v___x_3335_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__0;
    v___x_3336_ = l_Lean_stringToMessageData(v___x_3335_);
    return v___x_3336_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(
    mut v_a_3337_: *mut LeanObject,
    mut v___f_3338_: *mut LeanObject,
    mut v___f_3339_: *mut LeanObject,
    mut v___y_3340_: *mut LeanObject,
    mut v___y_3341_: *mut LeanObject,
    mut v___y_3342_: *mut LeanObject,
    mut v___y_3343_: *mut LeanObject,
    mut v___y_3344_: *mut LeanObject,
    mut v___y_3345_: *mut LeanObject,
    mut v___y_3346_: *mut LeanObject,
    mut v___y_3347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3361_: u8 = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3371_: u8 = 0;
    let mut v___x_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3375_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_a_3337_);
                v___x_3349_ = l_Lean_MVarId_getType(
                    v_a_3337_,
                    v___y_3344_,
                    v___y_3345_,
                    v___y_3346_,
                    v___y_3347_,
                );
                if lean_obj_tag(v___x_3349_) == 0 {
                    v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
                    lean_inc(v_a_3350_);
                    lean_dec_ref_known(v___x_3349_, 1);
                    v___x_3351_ = l_Lean_instantiateMVars___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__1___redArg(v_a_3350_, v___y_3345_);
                    v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
                    lean_inc(v_a_3352_);
                    lean_dec_ref(v___x_3351_);
                    v___x_3353_ = l_Lean_Elab_Tactic_Do_ProofMode_parseMGoal_x3f(v_a_3352_);
                    lean_dec(v_a_3352_);
                    if lean_obj_tag(v___x_3353_) == 1 {
                        v_val_3354_ = lean_ctor_get(v___x_3353_, 0);
                        lean_inc(v_val_3354_);
                        lean_dec_ref_known(v___x_3353_, 1);
                        v___x_3355_ = l_Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2(v_val_3354_, v___f_3338_, v___f_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
                        if lean_obj_tag(v___x_3355_) == 0 {
                            v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
                            lean_inc(v_a_3356_);
                            lean_dec_ref_known(v___x_3355_, 1);
                            v___x_3357_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(v_a_3337_, v_a_3356_, v___y_3345_);
                            return v___x_3357_;
                        } else {
                            lean_dec(v_a_3337_);
                            v_a_3358_ = lean_ctor_get(v___x_3355_, 0);
                            v_isSharedCheck_3365_ = (!lean_is_exclusive(v___x_3355_)) as u8;
                            if v_isSharedCheck_3365_ == 0 {
                                v___x_3360_ = v___x_3355_;
                                v_isShared_3361_ = v_isSharedCheck_3365_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3358_);
                                lean_dec(v___x_3355_);
                                v___x_3360_ = lean_box(0);
                                v_isShared_3361_ = v_isSharedCheck_3365_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_3353_);
                        lean_dec_ref(v___f_3339_);
                        lean_dec_ref(v___f_3338_);
                        lean_dec(v_a_3337_);
                        v___x_3366_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1), core::ptr::addr_of_mut!(l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1_once), _init_l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___closed__1);
                        v___x_3367_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(v___x_3366_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
                        return v___x_3367_;
                    }
                } else {
                    lean_dec_ref(v___f_3339_);
                    lean_dec_ref(v___f_3338_);
                    lean_dec(v_a_3337_);
                    v_a_3368_ = lean_ctor_get(v___x_3349_, 0);
                    v_isSharedCheck_3375_ = (!lean_is_exclusive(v___x_3349_)) as u8;
                    if v_isSharedCheck_3375_ == 0 {
                        v___x_3370_ = v___x_3349_;
                        v_isShared_3371_ = v_isSharedCheck_3375_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3368_);
                        lean_dec(v___x_3349_);
                        v___x_3370_ = lean_box(0);
                        v_isShared_3371_ = v_isSharedCheck_3375_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3361_ == 0 {
                    v___x_3363_ = v___x_3360_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
                    v___x_3363_ = v_reuseFailAlloc_3364_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3363_;
            }
            3 => {
                if v_isShared_3371_ == 0 {
                    v___x_3373_ = v___x_3370_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3374_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3374_, 0, v_a_3368_);
                    v___x_3373_ = v_reuseFailAlloc_3374_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed(
    mut v_a_3376_: *mut LeanObject,
    mut v___f_3377_: *mut LeanObject,
    mut v___f_3378_: *mut LeanObject,
    mut v___y_3379_: *mut LeanObject,
    mut v___y_3380_: *mut LeanObject,
    mut v___y_3381_: *mut LeanObject,
    mut v___y_3382_: *mut LeanObject,
    mut v___y_3383_: *mut LeanObject,
    mut v___y_3384_: *mut LeanObject,
    mut v___y_3385_: *mut LeanObject,
    mut v___y_3386_: *mut LeanObject,
    mut v___y_3387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3388_: *mut LeanObject = core::ptr::null_mut();
    v_res_3388_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2(
        v_a_3376_,
        v___f_3377_,
        v___f_3378_,
        v___y_3379_,
        v___y_3380_,
        v___y_3381_,
        v___y_3382_,
        v___y_3383_,
        v___y_3384_,
        v___y_3385_,
        v___y_3386_,
    );
    lean_dec(v___y_3386_);
    lean_dec_ref(v___y_3385_);
    lean_dec(v___y_3384_);
    lean_dec_ref(v___y_3383_);
    lean_dec(v___y_3382_);
    lean_dec_ref(v___y_3381_);
    lean_dec(v___y_3380_);
    lean_dec_ref(v___y_3379_);
    return v_res_3388_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(
    mut v_a_3391_: *mut LeanObject,
    mut v_a_3392_: *mut LeanObject,
    mut v_a_3393_: *mut LeanObject,
    mut v_a_3394_: *mut LeanObject,
    mut v_a_3395_: *mut LeanObject,
    mut v_a_3396_: *mut LeanObject,
    mut v_a_3397_: *mut LeanObject,
    mut v_a_3398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3409_: u8 = 0;
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3400_ = l_Lean_Elab_Tactic_getMainGoal___redArg(
                    v_a_3392_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_,
                );
                if lean_obj_tag(v___x_3400_) == 0 {
                    v_a_3401_ = lean_ctor_get(v___x_3400_, 0);
                    lean_inc_n(v_a_3401_, 2);
                    lean_dec_ref_known(v___x_3400_, 1);
                    v___f_3402_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__0;
                    v___f_3403_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___closed__1;
                    v___f_3404_ = lean_alloc_closure(
                        l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___lam__2___boxed
                            as *mut core::ffi::c_void,
                        12,
                        3,
                    );
                    lean_closure_set(v___f_3404_, 0, v_a_3401_);
                    lean_closure_set(v___f_3404_, 1, v___f_3402_);
                    lean_closure_set(v___f_3404_, 2, v___f_3403_);
                    v___x_3405_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__5___redArg(v_a_3401_, v___f_3404_, v_a_3391_, v_a_3392_, v_a_3393_, v_a_3394_, v_a_3395_, v_a_3396_, v_a_3397_, v_a_3398_);
                    return v___x_3405_;
                } else {
                    v_a_3406_ = lean_ctor_get(v___x_3400_, 0);
                    v_isSharedCheck_3413_ = (!lean_is_exclusive(v___x_3400_)) as u8;
                    if v_isSharedCheck_3413_ == 0 {
                        v___x_3408_ = v___x_3400_;
                        v_isShared_3409_ = v_isSharedCheck_3413_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3406_);
                        lean_dec(v___x_3400_);
                        v___x_3408_ = lean_box(0);
                        v_isShared_3409_ = v_isSharedCheck_3413_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3409_ == 0 {
                    v___x_3411_ = v___x_3408_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3412_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3412_, 0, v_a_3406_);
                    v___x_3411_ = v_reuseFailAlloc_3412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg___boxed(
    mut v_a_3414_: *mut LeanObject,
    mut v_a_3415_: *mut LeanObject,
    mut v_a_3416_: *mut LeanObject,
    mut v_a_3417_: *mut LeanObject,
    mut v_a_3418_: *mut LeanObject,
    mut v_a_3419_: *mut LeanObject,
    mut v_a_3420_: *mut LeanObject,
    mut v_a_3421_: *mut LeanObject,
    mut v_a_3422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3423_: *mut LeanObject = core::ptr::null_mut();
    v_res_3423_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(
        v_a_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_,
    );
    lean_dec(v_a_3421_);
    lean_dec_ref(v_a_3420_);
    lean_dec(v_a_3419_);
    lean_dec_ref(v_a_3418_);
    lean_dec(v_a_3417_);
    lean_dec_ref(v_a_3416_);
    lean_dec(v_a_3415_);
    lean_dec_ref(v_a_3414_);
    return v_res_3423_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(
    mut v_x_3424_: *mut LeanObject,
    mut v_a_3425_: *mut LeanObject,
    mut v_a_3426_: *mut LeanObject,
    mut v_a_3427_: *mut LeanObject,
    mut v_a_3428_: *mut LeanObject,
    mut v_a_3429_: *mut LeanObject,
    mut v_a_3430_: *mut LeanObject,
    mut v_a_3431_: *mut LeanObject,
    mut v_a_3432_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    v___x_3434_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___redArg(
        v_a_3425_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_,
    );
    return v___x_3434_;
}
pub unsafe fn l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed(
    mut v_x_3435_: *mut LeanObject,
    mut v_a_3436_: *mut LeanObject,
    mut v_a_3437_: *mut LeanObject,
    mut v_a_3438_: *mut LeanObject,
    mut v_a_3439_: *mut LeanObject,
    mut v_a_3440_: *mut LeanObject,
    mut v_a_3441_: *mut LeanObject,
    mut v_a_3442_: *mut LeanObject,
    mut v_a_3443_: *mut LeanObject,
    mut v_a_3444_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3445_: *mut LeanObject = core::ptr::null_mut();
    v_res_3445_ = l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame(
        v_x_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_,
        v_a_3443_,
    );
    lean_dec(v_a_3443_);
    lean_dec_ref(v_a_3442_);
    lean_dec(v_a_3441_);
    lean_dec_ref(v_a_3440_);
    lean_dec(v_a_3439_);
    lean_dec_ref(v_a_3438_);
    lean_dec(v_a_3437_);
    lean_dec_ref(v_a_3436_);
    lean_dec(v_x_3435_);
    return v_res_3445_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(
    mut v_00_u03b1_3446_: *mut LeanObject,
    mut v_msg_3447_: *mut LeanObject,
    mut v___y_3448_: *mut LeanObject,
    mut v___y_3449_: *mut LeanObject,
    mut v___y_3450_: *mut LeanObject,
    mut v___y_3451_: *mut LeanObject,
    mut v___y_3452_: *mut LeanObject,
    mut v___y_3453_: *mut LeanObject,
    mut v___y_3454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    v___x_3456_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___redArg(
            v_msg_3447_,
            v___y_3451_,
            v___y_3452_,
            v___y_3453_,
            v___y_3454_,
        );
    return v___x_3456_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0___boxed(
    mut v_00_u03b1_3457_: *mut LeanObject,
    mut v_msg_3458_: *mut LeanObject,
    mut v___y_3459_: *mut LeanObject,
    mut v___y_3460_: *mut LeanObject,
    mut v___y_3461_: *mut LeanObject,
    mut v___y_3462_: *mut LeanObject,
    mut v___y_3463_: *mut LeanObject,
    mut v___y_3464_: *mut LeanObject,
    mut v___y_3465_: *mut LeanObject,
    mut v___y_3466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3467_: *mut LeanObject = core::ptr::null_mut();
    v_res_3467_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__0(
        v_00_u03b1_3457_,
        v_msg_3458_,
        v___y_3459_,
        v___y_3460_,
        v___y_3461_,
        v___y_3462_,
        v___y_3463_,
        v___y_3464_,
        v___y_3465_,
    );
    lean_dec(v___y_3465_);
    lean_dec_ref(v___y_3464_);
    lean_dec(v___y_3463_);
    lean_dec_ref(v___y_3462_);
    lean_dec(v___y_3461_);
    lean_dec_ref(v___y_3460_);
    lean_dec(v___y_3459_);
    return v_res_3467_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(
    mut v_mvarId_3468_: *mut LeanObject,
    mut v_val_3469_: *mut LeanObject,
    mut v___y_3470_: *mut LeanObject,
    mut v___y_3471_: *mut LeanObject,
    mut v___y_3472_: *mut LeanObject,
    mut v___y_3473_: *mut LeanObject,
    mut v___y_3474_: *mut LeanObject,
    mut v___y_3475_: *mut LeanObject,
    mut v___y_3476_: *mut LeanObject,
    mut v___y_3477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    v___x_3479_ =
        l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___redArg(
            v_mvarId_3468_,
            v_val_3469_,
            v___y_3475_,
        );
    return v___x_3479_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3___boxed(
    mut v_mvarId_3480_: *mut LeanObject,
    mut v_val_3481_: *mut LeanObject,
    mut v___y_3482_: *mut LeanObject,
    mut v___y_3483_: *mut LeanObject,
    mut v___y_3484_: *mut LeanObject,
    mut v___y_3485_: *mut LeanObject,
    mut v___y_3486_: *mut LeanObject,
    mut v___y_3487_: *mut LeanObject,
    mut v___y_3488_: *mut LeanObject,
    mut v___y_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3491_: *mut LeanObject = core::ptr::null_mut();
    v_res_3491_ = l_Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3(
        v_mvarId_3480_,
        v_val_3481_,
        v___y_3482_,
        v___y_3483_,
        v___y_3484_,
        v___y_3485_,
        v___y_3486_,
        v___y_3487_,
        v___y_3488_,
        v___y_3489_,
    );
    lean_dec(v___y_3489_);
    lean_dec_ref(v___y_3488_);
    lean_dec(v___y_3487_);
    lean_dec_ref(v___y_3486_);
    lean_dec(v___y_3485_);
    lean_dec_ref(v___y_3484_);
    lean_dec(v___y_3483_);
    lean_dec_ref(v___y_3482_);
    return v_res_3491_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(
    mut v_00_u03b1_3492_: *mut LeanObject,
    mut v_msg_3493_: *mut LeanObject,
    mut v___y_3494_: *mut LeanObject,
    mut v___y_3495_: *mut LeanObject,
    mut v___y_3496_: *mut LeanObject,
    mut v___y_3497_: *mut LeanObject,
    mut v___y_3498_: *mut LeanObject,
    mut v___y_3499_: *mut LeanObject,
    mut v___y_3500_: *mut LeanObject,
    mut v___y_3501_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    v___x_3503_ =
        l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___redArg(
            v_msg_3493_,
            v___y_3498_,
            v___y_3499_,
            v___y_3500_,
            v___y_3501_,
        );
    return v___x_3503_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4___boxed(
    mut v_00_u03b1_3504_: *mut LeanObject,
    mut v_msg_3505_: *mut LeanObject,
    mut v___y_3506_: *mut LeanObject,
    mut v___y_3507_: *mut LeanObject,
    mut v___y_3508_: *mut LeanObject,
    mut v___y_3509_: *mut LeanObject,
    mut v___y_3510_: *mut LeanObject,
    mut v___y_3511_: *mut LeanObject,
    mut v___y_3512_: *mut LeanObject,
    mut v___y_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3515_: *mut LeanObject = core::ptr::null_mut();
    v_res_3515_ = l_Lean_throwError___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__4(
        v_00_u03b1_3504_,
        v_msg_3505_,
        v___y_3506_,
        v___y_3507_,
        v___y_3508_,
        v___y_3509_,
        v___y_3510_,
        v___y_3511_,
        v___y_3512_,
        v___y_3513_,
    );
    lean_dec(v___y_3513_);
    lean_dec_ref(v___y_3512_);
    lean_dec(v___y_3511_);
    lean_dec_ref(v___y_3510_);
    lean_dec(v___y_3509_);
    lean_dec_ref(v___y_3508_);
    lean_dec(v___y_3507_);
    lean_dec_ref(v___y_3506_);
    return v_res_3515_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(
    mut v_00_u03b1_3516_: *mut LeanObject,
    mut v_name_3517_: *mut LeanObject,
    mut v_bi_3518_: u8,
    mut v_type_3519_: *mut LeanObject,
    mut v_k_3520_: *mut LeanObject,
    mut v_kind_3521_: u8,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
    mut v___y_3524_: *mut LeanObject,
    mut v___y_3525_: *mut LeanObject,
    mut v___y_3526_: *mut LeanObject,
    mut v___y_3527_: *mut LeanObject,
    mut v___y_3528_: *mut LeanObject,
    mut v___y_3529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    v___x_3531_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___redArg(v_name_3517_, v_bi_3518_, v_type_3519_, v_k_3520_, v_kind_3521_, v___y_3522_, v___y_3523_, v___y_3524_, v___y_3525_, v___y_3526_, v___y_3527_, v___y_3528_, v___y_3529_);
    return v___x_3531_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5___boxed(
    mut v_00_u03b1_3532_: *mut LeanObject,
    mut v_name_3533_: *mut LeanObject,
    mut v_bi_3534_: *mut LeanObject,
    mut v_type_3535_: *mut LeanObject,
    mut v_k_3536_: *mut LeanObject,
    mut v_kind_3537_: *mut LeanObject,
    mut v___y_3538_: *mut LeanObject,
    mut v___y_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
    mut v___y_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
    mut v___y_3544_: *mut LeanObject,
    mut v___y_3545_: *mut LeanObject,
    mut v___y_3546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_bi_boxed_3547_: u8 = 0;
    let mut v_kind_boxed_3548_: u8 = 0;
    let mut v_res_3549_: *mut LeanObject = core::ptr::null_mut();
    v_bi_boxed_3547_ = (lean_unbox(v_bi_3534_) as u8);
    v_kind_boxed_3548_ = (lean_unbox(v_kind_3537_) as u8);
    v_res_3549_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3_spec__5(v_00_u03b1_3532_, v_name_3533_, v_bi_boxed_3547_, v_type_3535_, v_k_3536_, v_kind_boxed_3548_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
    lean_dec(v___y_3545_);
    lean_dec_ref(v___y_3544_);
    lean_dec(v___y_3543_);
    lean_dec_ref(v___y_3542_);
    lean_dec(v___y_3541_);
    lean_dec_ref(v___y_3540_);
    lean_dec(v___y_3539_);
    lean_dec_ref(v___y_3538_);
    return v_res_3549_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(
    mut v_00_u03b1_3550_: *mut LeanObject,
    mut v_name_3551_: *mut LeanObject,
    mut v_type_3552_: *mut LeanObject,
    mut v_k_3553_: *mut LeanObject,
    mut v___y_3554_: *mut LeanObject,
    mut v___y_3555_: *mut LeanObject,
    mut v___y_3556_: *mut LeanObject,
    mut v___y_3557_: *mut LeanObject,
    mut v___y_3558_: *mut LeanObject,
    mut v___y_3559_: *mut LeanObject,
    mut v___y_3560_: *mut LeanObject,
    mut v___y_3561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3563_: *mut LeanObject = core::ptr::null_mut();
    v___x_3563_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___redArg(v_name_3551_, v_type_3552_, v_k_3553_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
    return v___x_3563_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3___boxed(
    mut v_00_u03b1_3564_: *mut LeanObject,
    mut v_name_3565_: *mut LeanObject,
    mut v_type_3566_: *mut LeanObject,
    mut v_k_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
    mut v___y_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
    mut v___y_3575_: *mut LeanObject,
    mut v___y_3576_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3577_: *mut LeanObject = core::ptr::null_mut();
    v_res_3577_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Elab_Tactic_Do_ProofMode_mFrameCore___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__2_spec__3(v_00_u03b1_3564_, v_name_3565_, v_type_3566_, v_k_3567_, v___y_3568_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_);
    lean_dec(v___y_3575_);
    lean_dec_ref(v___y_3574_);
    lean_dec(v___y_3573_);
    lean_dec_ref(v___y_3572_);
    lean_dec(v___y_3571_);
    lean_dec_ref(v___y_3570_);
    lean_dec(v___y_3569_);
    lean_dec_ref(v___y_3568_);
    return v_res_3577_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5(
    mut v_00_u03b2_3578_: *mut LeanObject,
    mut v_x_3579_: *mut LeanObject,
    mut v_x_3580_: *mut LeanObject,
    mut v_x_3581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    v___x_3582_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5___redArg(v_x_3579_, v_x_3580_, v_x_3581_);
    return v___x_3582_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(
    mut v_00_u03b2_3583_: *mut LeanObject,
    mut v_x_3584_: *mut LeanObject,
    mut v_x_3585_: usize,
    mut v_x_3586_: usize,
    mut v_x_3587_: *mut LeanObject,
    mut v_x_3588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3589_: *mut LeanObject = core::ptr::null_mut();
    v___x_3589_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___redArg(v_x_3584_, v_x_3585_, v_x_3586_, v_x_3587_, v_x_3588_);
    return v___x_3589_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8___boxed(
    mut v_00_u03b2_3590_: *mut LeanObject,
    mut v_x_3591_: *mut LeanObject,
    mut v_x_3592_: *mut LeanObject,
    mut v_x_3593_: *mut LeanObject,
    mut v_x_3594_: *mut LeanObject,
    mut v_x_3595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_11934__boxed_3596_: usize = 0;
    let mut v_x_11935__boxed_3597_: usize = 0;
    let mut v_res_3598_: *mut LeanObject = core::ptr::null_mut();
    v_x_11934__boxed_3596_ = lean_unbox_usize(v_x_3592_);
    lean_dec(v_x_3592_);
    v_x_11935__boxed_3597_ = lean_unbox_usize(v_x_3593_);
    lean_dec(v_x_3593_);
    v_res_3598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8(v_00_u03b2_3590_, v_x_3591_, v_x_11934__boxed_3596_, v_x_11935__boxed_3597_, v_x_3594_, v_x_3595_);
    return v_res_3598_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10(
    mut v_00_u03b2_3599_: *mut LeanObject,
    mut v_n_3600_: *mut LeanObject,
    mut v_k_3601_: *mut LeanObject,
    mut v_v_3602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    v___x_3603_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10___redArg(v_n_3600_, v_k_3601_, v_v_3602_);
    return v___x_3603_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(
    mut v_00_u03b2_3604_: *mut LeanObject,
    mut v_depth_3605_: usize,
    mut v_keys_3606_: *mut LeanObject,
    mut v_vals_3607_: *mut LeanObject,
    mut v_heq_3608_: *mut LeanObject,
    mut v_i_3609_: *mut LeanObject,
    mut v_entries_3610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    v___x_3611_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___redArg(v_depth_3605_, v_keys_3606_, v_vals_3607_, v_i_3609_, v_entries_3610_);
    return v___x_3611_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11___boxed(
    mut v_00_u03b2_3612_: *mut LeanObject,
    mut v_depth_3613_: *mut LeanObject,
    mut v_keys_3614_: *mut LeanObject,
    mut v_vals_3615_: *mut LeanObject,
    mut v_heq_3616_: *mut LeanObject,
    mut v_i_3617_: *mut LeanObject,
    mut v_entries_3618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3619_: usize = 0;
    let mut v_res_3620_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3619_ = lean_unbox_usize(v_depth_3613_);
    lean_dec(v_depth_3613_);
    v_res_3620_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__11(v_00_u03b2_3612_, v_depth_boxed_3619_, v_keys_3614_, v_vals_3615_, v_heq_3616_, v_i_3617_, v_entries_3618_);
    lean_dec_ref(v_vals_3615_);
    lean_dec_ref(v_keys_3614_);
    return v_res_3620_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11(
    mut v_00_u03b2_3621_: *mut LeanObject,
    mut v_x_3622_: *mut LeanObject,
    mut v_x_3623_: *mut LeanObject,
    mut v_x_3624_: *mut LeanObject,
    mut v_x_3625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    v___x_3626_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Elab_Tactic_Do_ProofMode_elabMFrame_spec__3_spec__5_spec__8_spec__10_spec__11___redArg(v_x_3622_, v_x_3623_, v_x_3624_, v_x_3625_);
    return v___x_3626_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1()
-> *mut LeanObject {
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    v___x_3646_ = l_Lean_Elab_Tactic_tacticElabAttribute;
    v___x_3647_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__3;
    v___x_3648_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___closed__7;
    v___x_3649_ = lean_alloc_closure(
        l_Lean_Elab_Tactic_Do_ProofMode_elabMFrame___boxed as *mut core::ffi::c_void,
        10,
        0,
    );
    v___x_3650_ = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(
        v___x_3646_,
        v___x_3647_,
        v___x_3648_,
        v___x_3649_,
    );
    return v___x_3650_;
}
pub unsafe fn l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1___boxed(
    mut v_a_3651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3652_: *mut LeanObject = core::ptr::null_mut();
    v_res_3652_ = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
    return v_res_3652_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Elab_Tactic_Do_ProofMode_Frame_0__Lean_Elab_Tactic_Do_ProofMode_elabMFrame___regBuiltin_Lean_Elab_Tactic_Do_ProofMode_elabMFrame__1();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_Do_Syntax(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Elab_Tactic_Do_ProofMode_Focus(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Elab_Tactic_Do_ProofMode_Frame(builtin);
}
