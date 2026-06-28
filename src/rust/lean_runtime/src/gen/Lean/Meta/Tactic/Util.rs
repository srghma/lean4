// Lean compiler output
// Module: Lean.Meta.Tactic.Util
// Imports: Lean.Util.ForEachExprWhere Lean.Meta.PPGoal Lean.Meta.AppBuilder
use crate::r#gen::Init::Prelude::{
    l_Lean_MacroScopesView_review, l_Lean_Name_append, l_Lean_Name_hasMacroScopes,
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_num___override,
    l_Lean_Name_str___override, l_Lean_extractMacroScopes, l_Lean_maxRecDepthErrorMessage,
    lean_erase_macro_scopes,
};
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::lean_register_option;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_hash,
    l_Lean_Expr_headBeta, l_Lean_Expr_isFVar___boxed, l_Lean_instBEqFVarId_beq,
    l_Lean_instBEqMVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash, l_Lean_instHashableMVarId_hash, l_Lean_mkMVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_hasValue, l_Lean_LocalDecl_isImplementationDetail,
    l_Lean_LocalDecl_type, l_Lean_LocalDecl_value_x3f,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_kind, l_Lean_MessageData_note, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::AppBuilder::{
    initialize_Lean_Meta_AppBuilder, l_Lean_Meta_mkAppM, runtime_initialize_Lean_Meta_AppBuilder,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_getDecl,
    l_Lean_MVarId_setType___redArg, l_Lean_Meta_isExprDefEq, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_isProp;
use crate::r#gen::Lean::Meta::PPGoal::{
    initialize_Lean_Meta_PPGoal, runtime_initialize_Lean_Meta_PPGoal,
};
use crate::r#gen::Lean::Meta::Sorry::l_Lean_Meta_mkLabeledSorry;
use crate::r#gen::Lean::Meta::SynthInstance::l_Lean_Meta_synthInstance;
use crate::r#gen::Lean::MetavarContext::{
    l_Lean_MetavarContext_setMVarUserName, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::ForEachExprWhere::{
    initialize_Lean_Util_ForEachExprWhere, l_Lean_ForEachExprWhere_initCache,
    runtime_initialize_Lean_Util_ForEachExprWhere,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mod, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::lean_imports_rs::Lean::Expr::lean_expr_eqv;
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_6, lean_apply_7, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [100, 101, 98, 117, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanStringObject<23> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [116, 101, 114, 109, 105, 110, 97, 108, 84, 97, 99, 116, 105, 99, 115, 65, 115, 83, 111, 114, 114, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,16213016488940853032 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,10944533187742096104 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanStringObject<139> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 139, m_capacity: 139, m_length: 138, m_data: [119, 104, 101, 110, 32, 101, 110, 97, 98, 108, 101, 100, 44, 32, 116, 101, 114, 109, 105, 110, 97, 108, 32, 116, 97, 99, 116, 105, 99, 115, 32, 115, 117, 99, 104, 32, 97, 115, 32, 96, 103, 114, 105, 110, 100, 96, 32, 97, 110, 100, 32, 96, 111, 109, 101, 103, 97, 96, 32, 97, 114, 101, 32, 114, 101, 112, 108, 97, 99, 101, 100, 32, 119, 105, 116, 104, 32, 96, 115, 111, 114, 114, 121, 96, 46, 32, 85, 115, 101, 102, 117, 108, 32, 102, 111, 114, 32, 100, 101, 98, 117, 103, 103, 105, 110, 103, 32, 97, 110, 100, 32, 102, 105, 120, 105, 110, 103, 32, 98, 111, 111, 116, 115, 116, 114, 97, 112, 112, 105, 110, 103, 32, 105, 115, 115, 117, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [77, 101, 116, 97, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,11456239060754360645 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,3200922834059057545 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l_Lean_Meta_mkTacticExMsg___closed__0_value: LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [84, 97, 99, 116, 105, 99, 32, 96, 0],
};
static mut l_Lean_Meta_mkTacticExMsg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkTacticExMsg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_mkTacticExMsg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkTacticExMsg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkTacticExMsg___closed__2_value: LeanStringObject<11> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [96, 32, 102, 97, 105, 108, 101, 100, 58, 32, 0],
};
static mut l_Lean_Meta_mkTacticExMsg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkTacticExMsg___closed__2_value) as *mut LeanObject;
static mut l_Lean_Meta_mkTacticExMsg___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkTacticExMsg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_mkTacticExMsg___closed__4_value: LeanStringObject<3> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [10, 10, 0],
};
static mut l_Lean_Meta_mkTacticExMsg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_mkTacticExMsg___closed__4_value) as *mut LeanObject;
static mut l_Lean_Meta_mkTacticExMsg___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_mkTacticExMsg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_throwTacticEx___redArg___closed__0_value: LeanStringObject<11> =
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
        m_data: [96, 32, 102, 97, 105, 108, 101, 100, 10, 10, 0],
    };
static mut l_Lean_Meta_throwTacticEx___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwTacticEx___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_throwTacticEx___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_throwTacticEx___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value: LeanStringObject<31> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 31,
        m_capacity: 31,
        m_length: 30,
        m_data: [
            96, 32, 102, 97, 105, 108, 101, 100, 32, 119, 105, 116, 104, 32, 97, 32, 110, 101, 115,
            116, 101, 100, 32, 101, 114, 114, 111, 114, 58, 10, 0,
        ],
    };
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value: LeanStringObject<7> =
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
        m_data: [110, 101, 115, 116, 101, 100, 0],
    };
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__2_value)
                as *mut LeanObject,
            9884631923193754313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_throwNestedTacticEx___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__3_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1: usize = 0;
pub static l_Lean_MVarId_checkNotAssigned___closed__0_value: LeanStringObject<49> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 49,
        m_capacity: 49,
        m_length: 48,
        m_data: [
            84, 104, 101, 32, 109, 101, 116, 97, 118, 97, 114, 105, 97, 98, 108, 101, 32, 98, 101,
            108, 111, 119, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101,
            110, 32, 97, 115, 115, 105, 103, 110, 101, 100, 0,
        ],
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__0_value) as *mut LeanObject;
static mut l_Lean_MVarId_checkNotAssigned___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_checkNotAssigned___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_checkNotAssigned___closed__2_value: LeanStringObject<70> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 70,
        m_capacity: 70,
        m_length: 69,
        m_data: [
            84, 104, 105, 115, 32, 108, 105, 107, 101, 108, 121, 32, 105, 110, 100, 105, 99, 97,
            116, 101, 115, 32, 97, 110, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
            114, 111, 114, 32, 105, 110, 32, 116, 104, 105, 115, 32, 116, 97, 99, 116, 105, 99, 32,
            111, 114, 32, 97, 32, 112, 114, 105, 111, 114, 32, 111, 110, 101, 0,
        ],
    };
static mut l_Lean_MVarId_checkNotAssigned___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__2_value) as *mut LeanObject;
pub static l_Lean_MVarId_checkNotAssigned___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__2_value) as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_checkNotAssigned___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_checkNotAssigned___closed__3_value) as *mut LeanObject;
static mut l_Lean_MVarId_checkNotAssigned___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_checkNotAssigned___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_checkNotAssigned___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_checkNotAssigned___closed__5: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_checkNotAssigned___closed__6_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_checkNotAssigned___closed__6: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_MVarId_checkNotAssigned___closed__7_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_checkNotAssigned___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [84, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,142734480563613395 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,15847151208953044930 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,13556645696814629918 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,18261494228143523011 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [85, 116, 105, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,1826193737664319561 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,14998221293048064268 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,2824242023938616461 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,4283501524993450821 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,14927488885235163468 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,17596233699544133669 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,9760373788854647792 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,2995894122792280700 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,4482773431925144505 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,12438958728964694155 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,((( 1901113268 as usize) << 1) | 1) as *mut LeanObject,9603354042393261625 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,16753743204010399146 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,13532387658210436566 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,4161607161240432151 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2__value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_admit___closed__0_value: LeanStringObject<6> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [97, 100, 109, 105, 116, 0],
};
static mut l_Lean_MVarId_admit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_admit___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_admit___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_admit___closed__0_value) as *mut LeanObject,
        4924044685138168346 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_admit___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_admit___closed__1_value) as *mut LeanObject;
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0: usize = 0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Expr_isFVar___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 0, m_objs: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_MVarId_getNondepPropHyps___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_getNondepPropHyps___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_getNondepPropHyps___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_getNondepPropHyps___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_getNondepPropHyps___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_MVarId_getNondepPropHyps___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_MVarId_getNondepPropHyps___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_getNondepPropHyps___closed__1_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value) as *mut LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__0_value) as *mut LeanObject,7310567555909517314 as *mut LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__1_value) as *mut LeanObject,273128857561458264 as *mut LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2_value) as *mut LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_inferInstance___lam__0___closed__0_value: LeanStringObject<50> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 50,
        m_capacity: 50,
        m_length: 49,
        m_data: [
            96, 105, 110, 102, 101, 114, 95, 105, 110, 115, 116, 97, 110, 99, 101, 96, 32, 116, 97,
            99, 116, 105, 99, 32, 102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 97, 115, 115, 105,
            103, 110, 32, 105, 110, 115, 116, 97, 110, 99, 101, 0,
        ],
    };
static mut l_Lean_MVarId_inferInstance___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_inferInstance___lam__0___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_MVarId_inferInstance___lam__0___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_MVarId_inferInstance___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___lam__0___closed__1_value) as *mut LeanObject;
static mut l_Lean_MVarId_inferInstance___lam__0___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_inferInstance___lam__0___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_MVarId_inferInstance___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_MVarId_inferInstance___lam__0___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_MVarId_inferInstance___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        105, 110, 102, 101, 114, 95, 105, 110, 115, 116, 97, 110, 99, 101, 0,
    ],
};
static mut l_Lean_MVarId_inferInstance___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_inferInstance___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_inferInstance___closed__0_value) as *mut LeanObject,
        5120837411420157255 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_inferInstance___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_inferInstance___closed__1_value) as *mut LeanObject;
pub static l_Lean_MVarId_isSubsingleton___closed__0_value: LeanStringObject<13> =
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
        m_data: [83, 117, 98, 115, 105, 110, 103, 108, 101, 116, 111, 110, 0],
    };
static mut l_Lean_MVarId_isSubsingleton___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_isSubsingleton___closed__0_value) as *mut LeanObject;
pub static l_Lean_MVarId_isSubsingleton___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_MVarId_isSubsingleton___closed__0_value) as *mut LeanObject,
        13409365605382521367 as *mut LeanObject,
    ],
};
static mut l_Lean_MVarId_isSubsingleton___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_isSubsingleton___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 97, 99, 116, 105, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: LeanStringObject<22> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [115, 107, 105, 112, 65, 115, 115, 105, 103, 110, 101, 100, 73, 110, 115, 116, 97, 110, 99, 101, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject,16145843736367156323 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject,5414973503309327526 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: LeanStringObject<113> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 113, m_capacity: 113, m_length: 112, m_data: [105, 110, 32, 116, 104, 101, 32, 96, 114, 119, 96, 32, 97, 110, 100, 32, 96, 115, 105, 109, 112, 96, 32, 116, 97, 99, 116, 105, 99, 115, 44, 32, 105, 102, 32, 97, 110, 32, 105, 110, 115, 116, 97, 110, 99, 101, 32, 105, 109, 112, 108, 105, 99, 105, 116, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 105, 115, 32, 97, 115, 115, 105, 103, 110, 101, 100, 44, 32, 100, 111, 32, 110, 111, 116, 32, 116, 114, 121, 32, 116, 111, 32, 115, 121, 110, 116, 104, 101, 115, 105, 122, 101, 32, 105, 110, 115, 116, 97, 110, 99, 101, 46, 0]};
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__value) as *mut LeanObject,15449383196166861506 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject,9078769453211668998 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject,9140867362275919303 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4__value) as *mut LeanObject;
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(
    mut v_name_3789_: *mut LeanObject,
    mut v_decl_3790_: *mut LeanObject,
    mut v_ref_3791_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_defValue_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_descr_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_deprecation_x3f_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: u8 = 0;
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v___x_3803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3807_: u8 = 0;
    let mut v_unused_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3812_: u8 = 0;
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_defValue_3793_ = lean_ctor_get(v_decl_3790_, 0);
                v_descr_3794_ = lean_ctor_get(v_decl_3790_, 1);
                v_deprecation_x3f_3795_ = lean_ctor_get(v_decl_3790_, 2);
                v___x_3796_ = lean_alloc_ctor(1, 0, (1) as u32);
                v___x_3797_ = (lean_unbox(v_defValue_3793_) as u8);
                lean_ctor_set_uint8(v___x_3796_, 0 as u32, v___x_3797_);
                lean_inc(v_deprecation_x3f_3795_);
                lean_inc_ref(v_descr_3794_);
                lean_inc_n(v_name_3789_, 2);
                v___x_3798_ = lean_alloc_ctor(0, 5, (0) as u32);
                lean_ctor_set(v___x_3798_, 0, v_name_3789_);
                lean_ctor_set(v___x_3798_, 1, v_ref_3791_);
                lean_ctor_set(v___x_3798_, 2, v___x_3796_);
                lean_ctor_set(v___x_3798_, 3, v_descr_3794_);
                lean_ctor_set(v___x_3798_, 4, v_deprecation_x3f_3795_);
                v___x_3799_ = lean_register_option(v_name_3789_, v___x_3798_);
                if lean_obj_tag(v___x_3799_) == 0 {
                    v_isSharedCheck_3807_ = (!lean_is_exclusive(v___x_3799_)) as u8;
                    if v_isSharedCheck_3807_ == 0 {
                        v_unused_3808_ = lean_ctor_get(v___x_3799_, 0);
                        lean_dec(v_unused_3808_);
                        v___x_3801_ = v___x_3799_;
                        v_isShared_3802_ = v_isSharedCheck_3807_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3799_);
                        v___x_3801_ = lean_box(0);
                        v_isShared_3802_ = v_isSharedCheck_3807_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_name_3789_);
                    v_a_3809_ = lean_ctor_get(v___x_3799_, 0);
                    v_isSharedCheck_3816_ = (!lean_is_exclusive(v___x_3799_)) as u8;
                    if v_isSharedCheck_3816_ == 0 {
                        v___x_3811_ = v___x_3799_;
                        v_isShared_3812_ = v_isSharedCheck_3816_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3809_);
                        lean_dec(v___x_3799_);
                        v___x_3811_ = lean_box(0);
                        v_isShared_3812_ = v_isSharedCheck_3816_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_defValue_3793_);
                v___x_3803_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3803_, 0, v_name_3789_);
                lean_ctor_set(v___x_3803_, 1, v_defValue_3793_);
                if v_isShared_3802_ == 0 {
                    lean_ctor_set(v___x_3801_, 0, v___x_3803_);
                    v___x_3805_ = v___x_3801_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3806_, 0, v___x_3803_);
                    v___x_3805_ = v_reuseFailAlloc_3806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3805_;
            }
            3 => {
                if v_isShared_3812_ == 0 {
                    v___x_3814_ = v___x_3811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_a_3809_);
                    v___x_3814_ = v_reuseFailAlloc_3815_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0___boxed(
    mut v_name_3817_: *mut LeanObject,
    mut v_decl_3818_: *mut LeanObject,
    mut v_ref_3819_: *mut LeanObject,
    mut v_a_3820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3821_: *mut LeanObject = core::ptr::null_mut();
    v_res_3821_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v_name_3817_, v_decl_3818_, v_ref_3819_);
    lean_dec_ref(v_decl_3818_);
    return v_res_3821_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    v___x_3841_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_;
    v___x_3842_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_;
    v___x_3843_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_;
    v___x_3844_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_3841_, v___x_3842_, v___x_3843_);
    return v___x_3844_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4____boxed(
    mut v_a_3845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3846_: *mut LeanObject = core::ptr::null_mut();
    v_res_3846_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
    return v_res_3846_;
}
pub unsafe fn l_Lean_MVarId_getTag(
    mut v_mvarId_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
    mut v_a_3849_: *mut LeanObject,
    mut v_a_3850_: *mut LeanObject,
    mut v_a_3851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v_userName_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut v_a_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3866_: u8 = 0;
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3853_ = l_Lean_MVarId_getDecl(
                    v_mvarId_3847_,
                    v_a_3848_,
                    v_a_3849_,
                    v_a_3850_,
                    v_a_3851_,
                );
                if lean_obj_tag(v___x_3853_) == 0 {
                    v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
                    v_isSharedCheck_3862_ = (!lean_is_exclusive(v___x_3853_)) as u8;
                    if v_isSharedCheck_3862_ == 0 {
                        v___x_3856_ = v___x_3853_;
                        v_isShared_3857_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3854_);
                        lean_dec(v___x_3853_);
                        v___x_3856_ = lean_box(0);
                        v_isShared_3857_ = v_isSharedCheck_3862_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3863_ = lean_ctor_get(v___x_3853_, 0);
                    v_isSharedCheck_3870_ = (!lean_is_exclusive(v___x_3853_)) as u8;
                    if v_isSharedCheck_3870_ == 0 {
                        v___x_3865_ = v___x_3853_;
                        v_isShared_3866_ = v_isSharedCheck_3870_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3863_);
                        lean_dec(v___x_3853_);
                        v___x_3865_ = lean_box(0);
                        v_isShared_3866_ = v_isSharedCheck_3870_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_userName_3858_ = lean_ctor_get(v_a_3854_, 0);
                lean_inc(v_userName_3858_);
                lean_dec(v_a_3854_);
                if v_isShared_3857_ == 0 {
                    lean_ctor_set(v___x_3856_, 0, v_userName_3858_);
                    v___x_3860_ = v___x_3856_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3861_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_userName_3858_);
                    v___x_3860_ = v_reuseFailAlloc_3861_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3860_;
            }
            3 => {
                if v_isShared_3866_ == 0 {
                    v___x_3868_ = v___x_3865_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3869_, 0, v_a_3863_);
                    v___x_3868_ = v_reuseFailAlloc_3869_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_getTag___boxed(
    mut v_mvarId_3871_: *mut LeanObject,
    mut v_a_3872_: *mut LeanObject,
    mut v_a_3873_: *mut LeanObject,
    mut v_a_3874_: *mut LeanObject,
    mut v_a_3875_: *mut LeanObject,
    mut v_a_3876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3877_: *mut LeanObject = core::ptr::null_mut();
    v_res_3877_ = l_Lean_MVarId_getTag(v_mvarId_3871_, v_a_3872_, v_a_3873_, v_a_3874_, v_a_3875_);
    lean_dec(v_a_3875_);
    lean_dec_ref(v_a_3874_);
    lean_dec(v_a_3873_);
    lean_dec_ref(v_a_3872_);
    return v_res_3877_;
}
pub unsafe fn l_Lean_MVarId_setTag___redArg(
    mut v_mvarId_3878_: *mut LeanObject,
    mut v_tag_3879_: *mut LeanObject,
    mut v_a_3880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3890_: u8 = 0;
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3898_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3882_ = lean_st_ref_take(v_a_3880_);
                v_mctx_3883_ = lean_ctor_get(v___x_3882_, 0);
                v_cache_3884_ = lean_ctor_get(v___x_3882_, 1);
                v_zetaDeltaFVarIds_3885_ = lean_ctor_get(v___x_3882_, 2);
                v_postponed_3886_ = lean_ctor_get(v___x_3882_, 3);
                v_diag_3887_ = lean_ctor_get(v___x_3882_, 4);
                v_isSharedCheck_3898_ = (!lean_is_exclusive(v___x_3882_)) as u8;
                if v_isSharedCheck_3898_ == 0 {
                    v___x_3889_ = v___x_3882_;
                    v_isShared_3890_ = v_isSharedCheck_3898_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_3887_);
                    lean_inc(v_postponed_3886_);
                    lean_inc(v_zetaDeltaFVarIds_3885_);
                    lean_inc(v_cache_3884_);
                    lean_inc(v_mctx_3883_);
                    lean_dec(v___x_3882_);
                    v___x_3889_ = lean_box(0);
                    v_isShared_3890_ = v_isSharedCheck_3898_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3891_ = l_Lean_MetavarContext_setMVarUserName(
                    v_mctx_3883_,
                    v_mvarId_3878_,
                    v_tag_3879_,
                );
                if v_isShared_3890_ == 0 {
                    lean_ctor_set(v___x_3889_, 0, v___x_3891_);
                    v___x_3893_ = v___x_3889_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3891_);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_cache_3884_);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 2, v_zetaDeltaFVarIds_3885_);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 3, v_postponed_3886_);
                    lean_ctor_set(v_reuseFailAlloc_3897_, 4, v_diag_3887_);
                    v___x_3893_ = v_reuseFailAlloc_3897_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3894_ = lean_st_ref_set(v_a_3880_, v___x_3893_);
                v___x_3895_ = lean_box(0);
                v___x_3896_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3896_, 0, v___x_3895_);
                return v___x_3896_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_setTag___redArg___boxed(
    mut v_mvarId_3899_: *mut LeanObject,
    mut v_tag_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3903_: *mut LeanObject = core::ptr::null_mut();
    v_res_3903_ = l_Lean_MVarId_setTag___redArg(v_mvarId_3899_, v_tag_3900_, v_a_3901_);
    lean_dec(v_a_3901_);
    return v_res_3903_;
}
pub unsafe fn l_Lean_MVarId_setTag(
    mut v_mvarId_3904_: *mut LeanObject,
    mut v_tag_3905_: *mut LeanObject,
    mut v_a_3906_: *mut LeanObject,
    mut v_a_3907_: *mut LeanObject,
    mut v_a_3908_: *mut LeanObject,
    mut v_a_3909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3911_: *mut LeanObject = core::ptr::null_mut();
    v___x_3911_ = l_Lean_MVarId_setTag___redArg(v_mvarId_3904_, v_tag_3905_, v_a_3907_);
    return v___x_3911_;
}
pub unsafe fn l_Lean_MVarId_setTag___boxed(
    mut v_mvarId_3912_: *mut LeanObject,
    mut v_tag_3913_: *mut LeanObject,
    mut v_a_3914_: *mut LeanObject,
    mut v_a_3915_: *mut LeanObject,
    mut v_a_3916_: *mut LeanObject,
    mut v_a_3917_: *mut LeanObject,
    mut v_a_3918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3919_: *mut LeanObject = core::ptr::null_mut();
    v_res_3919_ = l_Lean_MVarId_setTag(
        v_mvarId_3912_,
        v_tag_3913_,
        v_a_3914_,
        v_a_3915_,
        v_a_3916_,
        v_a_3917_,
    );
    lean_dec(v_a_3917_);
    lean_dec_ref(v_a_3916_);
    lean_dec(v_a_3915_);
    lean_dec_ref(v_a_3914_);
    return v_res_3919_;
}
pub unsafe fn l_Lean_Meta_appendTag___lam__0(
    mut v_suffix_3920_: *mut LeanObject,
    mut v_x_3921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    v___x_3922_ = lean_erase_macro_scopes(v_suffix_3920_);
    v___x_3923_ = l_Lean_Name_append(v_x_3921_, v___x_3922_);
    return v___x_3923_;
}
pub unsafe fn l_Lean_Meta_appendTag(
    mut v_tag_3924_: *mut LeanObject,
    mut v_suffix_3925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3926_: u8 = 0;
    let mut v___x_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_view_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_imported_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctx_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_scopes_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3935_: u8 = 0;
    let mut v___x_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3926_ = l_Lean_Name_hasMacroScopes(v_tag_3924_);
                if v___x_3926_ == 0 {
                    v___x_3927_ = l_Lean_Meta_appendTag___lam__0(v_suffix_3925_, v_tag_3924_);
                    return v___x_3927_;
                } else {
                    v_view_3928_ = l_Lean_extractMacroScopes(v_tag_3924_);
                    v_name_3929_ = lean_ctor_get(v_view_3928_, 0);
                    v_imported_3930_ = lean_ctor_get(v_view_3928_, 1);
                    v_ctx_3931_ = lean_ctor_get(v_view_3928_, 2);
                    v_scopes_3932_ = lean_ctor_get(v_view_3928_, 3);
                    v_isSharedCheck_3941_ = (!lean_is_exclusive(v_view_3928_)) as u8;
                    if v_isSharedCheck_3941_ == 0 {
                        v___x_3934_ = v_view_3928_;
                        v_isShared_3935_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_scopes_3932_);
                        lean_inc(v_ctx_3931_);
                        lean_inc(v_imported_3930_);
                        lean_inc(v_name_3929_);
                        lean_dec(v_view_3928_);
                        v___x_3934_ = lean_box(0);
                        v_isShared_3935_ = v_isSharedCheck_3941_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3936_ = l_Lean_Meta_appendTag___lam__0(v_suffix_3925_, v_name_3929_);
                if v_isShared_3935_ == 0 {
                    lean_ctor_set(v___x_3934_, 0, v___x_3936_);
                    v___x_3938_ = v___x_3934_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3940_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3936_);
                    lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_imported_3930_);
                    lean_ctor_set(v_reuseFailAlloc_3940_, 2, v_ctx_3931_);
                    lean_ctor_set(v_reuseFailAlloc_3940_, 3, v_scopes_3932_);
                    v___x_3938_ = v_reuseFailAlloc_3940_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3939_ = l_Lean_MacroScopesView_review(v___x_3938_);
                return v___x_3939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_appendTagSuffix(
    mut v_mvarId_3942_: *mut LeanObject,
    mut v_suffix_3943_: *mut LeanObject,
    mut v_a_3944_: *mut LeanObject,
    mut v_a_3945_: *mut LeanObject,
    mut v_a_3946_: *mut LeanObject,
    mut v_a_3947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3956_: u8 = 0;
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3960_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_3942_);
                v___x_3949_ = l_Lean_MVarId_getTag(
                    v_mvarId_3942_,
                    v_a_3944_,
                    v_a_3945_,
                    v_a_3946_,
                    v_a_3947_,
                );
                if lean_obj_tag(v___x_3949_) == 0 {
                    v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
                    lean_inc(v_a_3950_);
                    lean_dec_ref_known(v___x_3949_, 1);
                    v___x_3951_ = l_Lean_Meta_appendTag(v_a_3950_, v_suffix_3943_);
                    v___x_3952_ =
                        l_Lean_MVarId_setTag___redArg(v_mvarId_3942_, v___x_3951_, v_a_3945_);
                    return v___x_3952_;
                } else {
                    lean_dec(v_suffix_3943_);
                    lean_dec(v_mvarId_3942_);
                    v_a_3953_ = lean_ctor_get(v___x_3949_, 0);
                    v_isSharedCheck_3960_ = (!lean_is_exclusive(v___x_3949_)) as u8;
                    if v_isSharedCheck_3960_ == 0 {
                        v___x_3955_ = v___x_3949_;
                        v_isShared_3956_ = v_isSharedCheck_3960_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3953_);
                        lean_dec(v___x_3949_);
                        v___x_3955_ = lean_box(0);
                        v_isShared_3956_ = v_isSharedCheck_3960_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3956_ == 0 {
                    v___x_3958_ = v___x_3955_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 0, v_a_3953_);
                    v___x_3958_ = v_reuseFailAlloc_3959_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3958_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_appendTagSuffix___boxed(
    mut v_mvarId_3961_: *mut LeanObject,
    mut v_suffix_3962_: *mut LeanObject,
    mut v_a_3963_: *mut LeanObject,
    mut v_a_3964_: *mut LeanObject,
    mut v_a_3965_: *mut LeanObject,
    mut v_a_3966_: *mut LeanObject,
    mut v_a_3967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3968_: *mut LeanObject = core::ptr::null_mut();
    v_res_3968_ = l_Lean_Meta_appendTagSuffix(
        v_mvarId_3961_,
        v_suffix_3962_,
        v_a_3963_,
        v_a_3964_,
        v_a_3965_,
        v_a_3966_,
    );
    lean_dec(v_a_3966_);
    lean_dec_ref(v_a_3965_);
    lean_dec(v_a_3964_);
    lean_dec_ref(v_a_3963_);
    return v_res_3968_;
}
pub unsafe fn l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
    mut v_type_3969_: *mut LeanObject,
    mut v_tag_3970_: *mut LeanObject,
    mut v_a_3971_: *mut LeanObject,
    mut v_a_3972_: *mut LeanObject,
    mut v_a_3973_: *mut LeanObject,
    mut v_a_3974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3977_: u8 = 0;
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    v___x_3976_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3976_, 0, v_type_3969_);
    v___x_3977_ = 2;
    v___x_3978_ = l_Lean_Meta_mkFreshExprMVar(
        v___x_3976_,
        v___x_3977_,
        v_tag_3970_,
        v_a_3971_,
        v_a_3972_,
        v_a_3973_,
        v_a_3974_,
    );
    return v___x_3978_;
}
pub unsafe fn l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar___boxed(
    mut v_type_3979_: *mut LeanObject,
    mut v_tag_3980_: *mut LeanObject,
    mut v_a_3981_: *mut LeanObject,
    mut v_a_3982_: *mut LeanObject,
    mut v_a_3983_: *mut LeanObject,
    mut v_a_3984_: *mut LeanObject,
    mut v_a_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3986_: *mut LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(
        v_type_3979_,
        v_tag_3980_,
        v_a_3981_,
        v_a_3982_,
        v_a_3983_,
        v_a_3984_,
    );
    lean_dec(v_a_3984_);
    lean_dec_ref(v_a_3983_);
    lean_dec(v_a_3982_);
    lean_dec_ref(v_a_3981_);
    return v_res_3986_;
}
pub unsafe fn _init_l_Lean_Meta_mkTacticExMsg___closed__1() -> *mut LeanObject {
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    v___x_3988_ = l_Lean_Meta_mkTacticExMsg___closed__0;
    v___x_3989_ = l_Lean_stringToMessageData(v___x_3988_);
    return v___x_3989_;
}
pub unsafe fn _init_l_Lean_Meta_mkTacticExMsg___closed__3() -> *mut LeanObject {
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3991_ = l_Lean_Meta_mkTacticExMsg___closed__2;
    v___x_3992_ = l_Lean_stringToMessageData(v___x_3991_);
    return v___x_3992_;
}
pub unsafe fn _init_l_Lean_Meta_mkTacticExMsg___closed__5() -> *mut LeanObject {
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    v___x_3994_ = l_Lean_Meta_mkTacticExMsg___closed__4;
    v___x_3995_ = l_Lean_stringToMessageData(v___x_3994_);
    return v___x_3995_;
}
pub unsafe fn l_Lean_Meta_mkTacticExMsg(
    mut v_tacticName_3996_: *mut LeanObject,
    mut v_mvarId_3997_: *mut LeanObject,
    mut v_msg_3998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4008_: *mut LeanObject = core::ptr::null_mut();
    v___x_3999_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__1,
    );
    v___x_4000_ = l_Lean_MessageData_ofName(v_tacticName_3996_);
    v___x_4001_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4001_, 0, v___x_3999_);
    lean_ctor_set(v___x_4001_, 1, v___x_4000_);
    v___x_4002_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__3_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__3,
    );
    v___x_4003_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4003_, 0, v___x_4001_);
    lean_ctor_set(v___x_4003_, 1, v___x_4002_);
    v___x_4004_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4004_, 0, v___x_4003_);
    lean_ctor_set(v___x_4004_, 1, v_msg_3998_);
    v___x_4005_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__5_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__5,
    );
    v___x_4006_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4006_, 0, v___x_4004_);
    lean_ctor_set(v___x_4006_, 1, v___x_4005_);
    v___x_4007_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4007_, 0, v_mvarId_3997_);
    v___x_4008_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4008_, 0, v___x_4006_);
    lean_ctor_set(v___x_4008_, 1, v___x_4007_);
    return v___x_4008_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(
    mut v_msgData_4009_: *mut LeanObject,
    mut v___y_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    v___x_4015_ = lean_st_ref_get(v___y_4013_);
    v_env_4016_ = lean_ctor_get(v___x_4015_, 0);
    lean_inc_ref(v_env_4016_);
    lean_dec(v___x_4015_);
    v___x_4017_ = lean_st_ref_get(v___y_4011_);
    v_mctx_4018_ = lean_ctor_get(v___x_4017_, 0);
    lean_inc_ref(v_mctx_4018_);
    lean_dec(v___x_4017_);
    v_lctx_4019_ = lean_ctor_get(v___y_4010_, 2);
    v_options_4020_ = lean_ctor_get(v___y_4012_, 2);
    lean_inc_ref(v_options_4020_);
    lean_inc_ref(v_lctx_4019_);
    v___x_4021_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_4021_, 0, v_env_4016_);
    lean_ctor_set(v___x_4021_, 1, v_mctx_4018_);
    lean_ctor_set(v___x_4021_, 2, v_lctx_4019_);
    lean_ctor_set(v___x_4021_, 3, v_options_4020_);
    v___x_4022_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4022_, 0, v___x_4021_);
    lean_ctor_set(v___x_4022_, 1, v_msgData_4009_);
    v___x_4023_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4023_, 0, v___x_4022_);
    return v___x_4023_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0___boxed(
    mut v_msgData_4024_: *mut LeanObject,
    mut v___y_4025_: *mut LeanObject,
    mut v___y_4026_: *mut LeanObject,
    mut v___y_4027_: *mut LeanObject,
    mut v___y_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4030_: *mut LeanObject = core::ptr::null_mut();
    v_res_4030_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msgData_4024_, v___y_4025_, v___y_4026_, v___y_4027_, v___y_4028_);
    lean_dec(v___y_4028_);
    lean_dec_ref(v___y_4027_);
    lean_dec(v___y_4026_);
    lean_dec_ref(v___y_4025_);
    return v_res_4030_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
    mut v_msg_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4042_: u8 = 0;
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_4037_ = lean_ctor_get(v___y_4034_, 5);
                v___x_4038_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0_spec__0(v_msg_4031_, v___y_4032_, v___y_4033_, v___y_4034_, v___y_4035_);
                v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
                v_isSharedCheck_4047_ = (!lean_is_exclusive(v___x_4038_)) as u8;
                if v_isSharedCheck_4047_ == 0 {
                    v___x_4041_ = v___x_4038_;
                    v_isShared_4042_ = v_isSharedCheck_4047_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4039_);
                    lean_dec(v___x_4038_);
                    v___x_4041_ = lean_box(0);
                    v_isShared_4042_ = v_isSharedCheck_4047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_4037_);
                v___x_4043_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4043_, 0, v_ref_4037_);
                lean_ctor_set(v___x_4043_, 1, v_a_4039_);
                if v_isShared_4042_ == 0 {
                    lean_ctor_set_tag(v___x_4041_, 1);
                    lean_ctor_set(v___x_4041_, 0, v___x_4043_);
                    v___x_4045_ = v___x_4041_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4046_, 0, v___x_4043_);
                    v___x_4045_ = v_reuseFailAlloc_4046_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg___boxed(
    mut v_msg_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
    mut v___y_4050_: *mut LeanObject,
    mut v___y_4051_: *mut LeanObject,
    mut v___y_4052_: *mut LeanObject,
    mut v___y_4053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4054_: *mut LeanObject = core::ptr::null_mut();
    v_res_4054_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
        v_msg_4048_,
        v___y_4049_,
        v___y_4050_,
        v___y_4051_,
        v___y_4052_,
    );
    lean_dec(v___y_4052_);
    lean_dec_ref(v___y_4051_);
    lean_dec(v___y_4050_);
    lean_dec_ref(v___y_4049_);
    return v_res_4054_;
}
pub unsafe fn _init_l_Lean_Meta_throwTacticEx___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    v___x_4056_ = l_Lean_Meta_throwTacticEx___redArg___closed__0;
    v___x_4057_ = l_Lean_stringToMessageData(v___x_4056_);
    return v___x_4057_;
}
pub unsafe fn l_Lean_Meta_throwTacticEx___redArg(
    mut v_tacticName_4058_: *mut LeanObject,
    mut v_mvarId_4059_: *mut LeanObject,
    mut v_msg_x3f_4060_: *mut LeanObject,
    mut v_a_4061_: *mut LeanObject,
    mut v_a_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
    mut v_a_4064_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_msg_x3f_4060_) == 0 {
        let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4067_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
        v___x_4066_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1_once),
            _init_l_Lean_Meta_mkTacticExMsg___closed__1,
        );
        v___x_4067_ = l_Lean_MessageData_ofName(v_tacticName_4058_);
        v___x_4068_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_4068_, 0, v___x_4066_);
        lean_ctor_set(v___x_4068_, 1, v___x_4067_);
        v___x_4069_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Meta_throwTacticEx___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Lean_Meta_throwTacticEx___redArg___closed__1_once),
            _init_l_Lean_Meta_throwTacticEx___redArg___closed__1,
        );
        v___x_4070_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_4070_, 0, v___x_4068_);
        lean_ctor_set(v___x_4070_, 1, v___x_4069_);
        v___x_4071_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_4071_, 0, v_mvarId_4059_);
        v___x_4072_ = lean_alloc_ctor(7, 2, (0) as u32);
        lean_ctor_set(v___x_4072_, 0, v___x_4070_);
        lean_ctor_set(v___x_4072_, 1, v___x_4071_);
        v___x_4073_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
            v___x_4072_,
            v_a_4061_,
            v_a_4062_,
            v_a_4063_,
            v_a_4064_,
        );
        return v___x_4073_;
    } else {
        let mut v_val_4074_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
        v_val_4074_ = lean_ctor_get(v_msg_x3f_4060_, 0);
        lean_inc(v_val_4074_);
        lean_dec_ref_known(v_msg_x3f_4060_, 1);
        v___x_4075_ = l_Lean_Meta_mkTacticExMsg(v_tacticName_4058_, v_mvarId_4059_, v_val_4074_);
        v___x_4076_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
            v___x_4075_,
            v_a_4061_,
            v_a_4062_,
            v_a_4063_,
            v_a_4064_,
        );
        return v___x_4076_;
    }
}
pub unsafe fn l_Lean_Meta_throwTacticEx___redArg___boxed(
    mut v_tacticName_4077_: *mut LeanObject,
    mut v_mvarId_4078_: *mut LeanObject,
    mut v_msg_x3f_4079_: *mut LeanObject,
    mut v_a_4080_: *mut LeanObject,
    mut v_a_4081_: *mut LeanObject,
    mut v_a_4082_: *mut LeanObject,
    mut v_a_4083_: *mut LeanObject,
    mut v_a_4084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4085_: *mut LeanObject = core::ptr::null_mut();
    v_res_4085_ = l_Lean_Meta_throwTacticEx___redArg(
        v_tacticName_4077_,
        v_mvarId_4078_,
        v_msg_x3f_4079_,
        v_a_4080_,
        v_a_4081_,
        v_a_4082_,
        v_a_4083_,
    );
    lean_dec(v_a_4083_);
    lean_dec_ref(v_a_4082_);
    lean_dec(v_a_4081_);
    lean_dec_ref(v_a_4080_);
    return v_res_4085_;
}
pub unsafe fn l_Lean_Meta_throwTacticEx(
    mut v_00_u03b1_4086_: *mut LeanObject,
    mut v_tacticName_4087_: *mut LeanObject,
    mut v_mvarId_4088_: *mut LeanObject,
    mut v_msg_x3f_4089_: *mut LeanObject,
    mut v_a_4090_: *mut LeanObject,
    mut v_a_4091_: *mut LeanObject,
    mut v_a_4092_: *mut LeanObject,
    mut v_a_4093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    v___x_4095_ = l_Lean_Meta_throwTacticEx___redArg(
        v_tacticName_4087_,
        v_mvarId_4088_,
        v_msg_x3f_4089_,
        v_a_4090_,
        v_a_4091_,
        v_a_4092_,
        v_a_4093_,
    );
    return v___x_4095_;
}
pub unsafe fn l_Lean_Meta_throwTacticEx___boxed(
    mut v_00_u03b1_4096_: *mut LeanObject,
    mut v_tacticName_4097_: *mut LeanObject,
    mut v_mvarId_4098_: *mut LeanObject,
    mut v_msg_x3f_4099_: *mut LeanObject,
    mut v_a_4100_: *mut LeanObject,
    mut v_a_4101_: *mut LeanObject,
    mut v_a_4102_: *mut LeanObject,
    mut v_a_4103_: *mut LeanObject,
    mut v_a_4104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4105_: *mut LeanObject = core::ptr::null_mut();
    v_res_4105_ = l_Lean_Meta_throwTacticEx(
        v_00_u03b1_4096_,
        v_tacticName_4097_,
        v_mvarId_4098_,
        v_msg_x3f_4099_,
        v_a_4100_,
        v_a_4101_,
        v_a_4102_,
        v_a_4103_,
    );
    lean_dec(v_a_4103_);
    lean_dec_ref(v_a_4102_);
    lean_dec(v_a_4101_);
    lean_dec_ref(v_a_4100_);
    return v_res_4105_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(
    mut v_00_u03b1_4106_: *mut LeanObject,
    mut v_msg_4107_: *mut LeanObject,
    mut v___y_4108_: *mut LeanObject,
    mut v___y_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    v___x_4113_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
        v_msg_4107_,
        v___y_4108_,
        v___y_4109_,
        v___y_4110_,
        v___y_4111_,
    );
    return v___x_4113_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___boxed(
    mut v_00_u03b1_4114_: *mut LeanObject,
    mut v_msg_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4121_: *mut LeanObject = core::ptr::null_mut();
    v_res_4121_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0(
        v_00_u03b1_4114_,
        v_msg_4115_,
        v___y_4116_,
        v___y_4117_,
        v___y_4118_,
        v___y_4119_,
    );
    lean_dec(v___y_4119_);
    lean_dec_ref(v___y_4118_);
    lean_dec(v___y_4117_);
    lean_dec_ref(v___y_4116_);
    return v_res_4121_;
}
pub unsafe fn _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1() -> *mut LeanObject {
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    v___x_4123_ = l_Lean_Meta_throwNestedTacticEx___redArg___closed__0;
    v___x_4124_ = l_Lean_stringToMessageData(v___x_4123_);
    return v___x_4124_;
}
pub unsafe fn l_Lean_Meta_throwNestedTacticEx___redArg(
    mut v_tacticName_4128_: *mut LeanObject,
    mut v_ex_4129_: *mut LeanObject,
    mut v_a_4130_: *mut LeanObject,
    mut v_a_4131_: *mut LeanObject,
    mut v_a_4132_: *mut LeanObject,
    mut v_a_4133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_nestedMsg_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_msg_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_kind_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: u8 = 0;
    v_nestedMsg_4135_ = l_Lean_Exception_toMessageData(v_ex_4129_);
    v___x_4136_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_mkTacticExMsg___closed__1_once),
        _init_l_Lean_Meta_mkTacticExMsg___closed__1,
    );
    v___x_4137_ = l_Lean_MessageData_ofName(v_tacticName_4128_);
    v___x_4138_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4138_, 0, v___x_4136_);
    lean_ctor_set(v___x_4138_, 1, v___x_4137_);
    v___x_4139_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_throwNestedTacticEx___redArg___closed__1_once),
        _init_l_Lean_Meta_throwNestedTacticEx___redArg___closed__1,
    );
    v___x_4140_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4140_, 0, v___x_4138_);
    lean_ctor_set(v___x_4140_, 1, v___x_4139_);
    lean_inc_ref(v_nestedMsg_4135_);
    v_msg_4141_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v_msg_4141_, 0, v___x_4140_);
    lean_ctor_set(v_msg_4141_, 1, v_nestedMsg_4135_);
    v_kind_4142_ = l_Lean_MessageData_kind(v_nestedMsg_4135_);
    lean_dec_ref(v_nestedMsg_4135_);
    v___x_4143_ = l_Lean_Name_isAnonymous(v_kind_4142_);
    if v___x_4143_ == 0 {
        let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4147_: *mut LeanObject = core::ptr::null_mut();
        v___x_4144_ = l_Lean_Meta_throwNestedTacticEx___redArg___closed__3;
        v___x_4145_ = l_Lean_Name_append(v___x_4144_, v_kind_4142_);
        v___x_4146_ = lean_alloc_ctor(8, 2, (0) as u32);
        lean_ctor_set(v___x_4146_, 0, v___x_4145_);
        lean_ctor_set(v___x_4146_, 1, v_msg_4141_);
        v___x_4147_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
            v___x_4146_,
            v_a_4130_,
            v_a_4131_,
            v_a_4132_,
            v_a_4133_,
        );
        return v___x_4147_;
    } else {
        let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_kind_4142_);
        v___x_4148_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
            v_msg_4141_,
            v_a_4130_,
            v_a_4131_,
            v_a_4132_,
            v_a_4133_,
        );
        return v___x_4148_;
    }
}
pub unsafe fn l_Lean_Meta_throwNestedTacticEx___redArg___boxed(
    mut v_tacticName_4149_: *mut LeanObject,
    mut v_ex_4150_: *mut LeanObject,
    mut v_a_4151_: *mut LeanObject,
    mut v_a_4152_: *mut LeanObject,
    mut v_a_4153_: *mut LeanObject,
    mut v_a_4154_: *mut LeanObject,
    mut v_a_4155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4156_: *mut LeanObject = core::ptr::null_mut();
    v_res_4156_ = l_Lean_Meta_throwNestedTacticEx___redArg(
        v_tacticName_4149_,
        v_ex_4150_,
        v_a_4151_,
        v_a_4152_,
        v_a_4153_,
        v_a_4154_,
    );
    lean_dec(v_a_4154_);
    lean_dec_ref(v_a_4153_);
    lean_dec(v_a_4152_);
    lean_dec_ref(v_a_4151_);
    return v_res_4156_;
}
pub unsafe fn l_Lean_Meta_throwNestedTacticEx(
    mut v_00_u03b1_4157_: *mut LeanObject,
    mut v_tacticName_4158_: *mut LeanObject,
    mut v_ex_4159_: *mut LeanObject,
    mut v_a_4160_: *mut LeanObject,
    mut v_a_4161_: *mut LeanObject,
    mut v_a_4162_: *mut LeanObject,
    mut v_a_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_Lean_Meta_throwNestedTacticEx___redArg(
        v_tacticName_4158_,
        v_ex_4159_,
        v_a_4160_,
        v_a_4161_,
        v_a_4162_,
        v_a_4163_,
    );
    return v___x_4165_;
}
pub unsafe fn l_Lean_Meta_throwNestedTacticEx___boxed(
    mut v_00_u03b1_4166_: *mut LeanObject,
    mut v_tacticName_4167_: *mut LeanObject,
    mut v_ex_4168_: *mut LeanObject,
    mut v_a_4169_: *mut LeanObject,
    mut v_a_4170_: *mut LeanObject,
    mut v_a_4171_: *mut LeanObject,
    mut v_a_4172_: *mut LeanObject,
    mut v_a_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4174_: *mut LeanObject = core::ptr::null_mut();
    v_res_4174_ = l_Lean_Meta_throwNestedTacticEx(
        v_00_u03b1_4166_,
        v_tacticName_4167_,
        v_ex_4168_,
        v_a_4169_,
        v_a_4170_,
        v_a_4171_,
        v_a_4172_,
    );
    lean_dec(v_a_4172_);
    lean_dec_ref(v_a_4171_);
    lean_dec(v_a_4170_);
    lean_dec_ref(v_a_4169_);
    return v_res_4174_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_keys_4175_: *mut LeanObject,
    mut v_i_4176_: *mut LeanObject,
    mut v_k_4177_: *mut LeanObject,
) -> u8 {
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4179_: u8 = 0;
    let mut v_k_x27_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: u8 = 0;
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4178_ = lean_array_get_size(v_keys_4175_);
                v___x_4179_ = lean_nat_dec_lt(v_i_4176_, v___x_4178_);
                if v___x_4179_ == 0 {
                    lean_dec(v_i_4176_);
                    return v___x_4179_;
                } else {
                    v_k_x27_4180_ = lean_array_fget_borrowed(v_keys_4175_, v_i_4176_);
                    v___x_4181_ = l_Lean_instBEqMVarId_beq(v_k_4177_, v_k_x27_4180_);
                    if v___x_4181_ == 0 {
                        v___x_4182_ = lean_unsigned_to_nat(1);
                        v___x_4183_ = lean_nat_add(v_i_4176_, v___x_4182_);
                        lean_dec(v_i_4176_);
                        v_i_4176_ = v___x_4183_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_i_4176_);
                        return v___x_4181_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg___boxed(
    mut v_keys_4185_: *mut LeanObject,
    mut v_i_4186_: *mut LeanObject,
    mut v_k_4187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4188_: u8 = 0;
    let mut v_r_4189_: *mut LeanObject = core::ptr::null_mut();
    v_res_4188_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4185_, v_i_4186_, v_k_4187_);
    lean_dec(v_k_4187_);
    lean_dec_ref(v_keys_4185_);
    v_r_4189_ = lean_box((v_res_4188_) as usize);
    return v_r_4189_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_4190_: usize = 0;
    let mut v___x_4191_: usize = 0;
    let mut v___x_4192_: usize = 0;
    v___x_4190_ = 5usize;
    v___x_4191_ = 1usize;
    v___x_4192_ = lean_usize_shift_left(v___x_4191_, v___x_4190_);
    return v___x_4192_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_4193_: usize = 0;
    let mut v___x_4194_: usize = 0;
    let mut v___x_4195_: usize = 0;
    v___x_4193_ = 1usize;
    v___x_4194_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__0);
    v___x_4195_ = lean_usize_sub(v___x_4194_, v___x_4193_);
    return v___x_4195_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(
    mut v_x_4196_: *mut LeanObject,
    mut v_x_4197_: usize,
    mut v_x_4198_: *mut LeanObject,
) -> u8 {
    let mut v_es_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: usize = 0;
    let mut v___x_4202_: usize = 0;
    let mut v___x_4203_: usize = 0;
    let mut v_j_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: u8 = 0;
    let mut v_node_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: usize = 0;
    let mut v___x_4211_: u8 = 0;
    let mut v_ks_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4196_) == 0 {
                    v_es_4199_ = lean_ctor_get(v_x_4196_, 0);
                    v___x_4200_ = lean_box(2);
                    v___x_4201_ = 5usize;
                    v___x_4202_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4203_ = lean_usize_land(v_x_4197_, v___x_4202_);
                    v_j_4204_ = lean_usize_to_nat(v___x_4203_);
                    v___x_4205_ = lean_array_get_borrowed(v___x_4200_, v_es_4199_, v_j_4204_);
                    lean_dec(v_j_4204_);
                    match lean_obj_tag(v___x_4205_) {
                        0 => {
                            v_key_4206_ = lean_ctor_get(v___x_4205_, 0);
                            v___x_4207_ = l_Lean_instBEqMVarId_beq(v_x_4198_, v_key_4206_);
                            return v___x_4207_;
                        }
                        1 => {
                            v_node_4208_ = lean_ctor_get(v___x_4205_, 0);
                            v___x_4209_ = lean_usize_shift_right(v_x_4197_, v___x_4201_);
                            v_x_4196_ = v_node_4208_;
                            v_x_4197_ = v___x_4209_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4211_ = 0;
                            return v___x_4211_;
                        }
                    }
                } else {
                    v_ks_4212_ = lean_ctor_get(v_x_4196_, 0);
                    v___x_4213_ = lean_unsigned_to_nat(0);
                    v___x_4214_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4212_, v___x_4213_, v_x_4198_);
                    return v___x_4214_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_x_4215_: *mut LeanObject,
    mut v_x_4216_: *mut LeanObject,
    mut v_x_4217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_596__boxed_4218_: usize = 0;
    let mut v_res_4219_: u8 = 0;
    let mut v_r_4220_: *mut LeanObject = core::ptr::null_mut();
    v_x_596__boxed_4218_ = lean_unbox_usize(v_x_4216_);
    lean_dec(v_x_4216_);
    v_res_4219_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_4215_, v_x_596__boxed_4218_, v_x_4217_);
    lean_dec(v_x_4217_);
    lean_dec_ref(v_x_4215_);
    v_r_4220_ = lean_box((v_res_4219_) as usize);
    return v_r_4220_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(
    mut v_x_4221_: *mut LeanObject,
    mut v_x_4222_: *mut LeanObject,
) -> u8 {
    let mut v___x_4223_: u64 = 0;
    let mut v___x_4224_: usize = 0;
    let mut v___x_4225_: u8 = 0;
    v___x_4223_ = l_Lean_instHashableMVarId_hash(v_x_4222_);
    v___x_4224_ = lean_uint64_to_usize(v___x_4223_);
    v___x_4225_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_4221_, v___x_4224_, v_x_4222_);
    return v___x_4225_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg___boxed(
    mut v_x_4226_: *mut LeanObject,
    mut v_x_4227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4228_: u8 = 0;
    let mut v_r_4229_: *mut LeanObject = core::ptr::null_mut();
    v_res_4228_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_4226_, v_x_4227_);
    lean_dec(v_x_4227_);
    lean_dec_ref(v_x_4226_);
    v_r_4229_ = lean_box((v_res_4228_) as usize);
    return v_r_4229_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(
    mut v_mvarId_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: u8 = 0;
    let mut v___x_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    v___x_4233_ = lean_st_ref_get(v___y_4231_);
    v_mctx_4234_ = lean_ctor_get(v___x_4233_, 0);
    lean_inc_ref(v_mctx_4234_);
    lean_dec(v___x_4233_);
    v_eAssignment_4235_ = lean_ctor_get(v_mctx_4234_, 8);
    lean_inc_ref(v_eAssignment_4235_);
    lean_dec_ref(v_mctx_4234_);
    v___x_4236_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_eAssignment_4235_, v_mvarId_4230_);
    lean_dec_ref(v_eAssignment_4235_);
    v___x_4237_ = lean_box((v___x_4236_) as usize);
    v___x_4238_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4238_, 0, v___x_4237_);
    return v___x_4238_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg___boxed(
    mut v_mvarId_4239_: *mut LeanObject,
    mut v___y_4240_: *mut LeanObject,
    mut v___y_4241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4242_: *mut LeanObject = core::ptr::null_mut();
    v_res_4242_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(
        v_mvarId_4239_,
        v___y_4240_,
    );
    lean_dec(v___y_4240_);
    lean_dec(v_mvarId_4239_);
    return v_res_4242_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__1() -> *mut LeanObject {
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    v___x_4244_ = l_Lean_MVarId_checkNotAssigned___closed__0;
    v___x_4245_ = l_Lean_stringToMessageData(v___x_4244_);
    return v___x_4245_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__4() -> *mut LeanObject {
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    v___x_4249_ = l_Lean_MVarId_checkNotAssigned___closed__3;
    v___x_4250_ = l_Lean_MessageData_ofFormat(v___x_4249_);
    return v___x_4250_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__5() -> *mut LeanObject {
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut LeanObject = core::ptr::null_mut();
    v___x_4251_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__4),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__4_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__4,
    );
    v___x_4252_ = l_Lean_MessageData_note(v___x_4251_);
    return v___x_4252_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__6() -> *mut LeanObject {
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    v___x_4253_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__5),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__5_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__5,
    );
    v___x_4254_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__1),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__1_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__1,
    );
    v___x_4255_ = lean_alloc_ctor(7, 2, (0) as u32);
    lean_ctor_set(v___x_4255_, 0, v___x_4254_);
    lean_ctor_set(v___x_4255_, 1, v___x_4253_);
    return v___x_4255_;
}
pub unsafe fn _init_l_Lean_MVarId_checkNotAssigned___closed__7() -> *mut LeanObject {
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    v___x_4256_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__6),
        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__6_once),
        _init_l_Lean_MVarId_checkNotAssigned___closed__6,
    );
    v___x_4257_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4257_, 0, v___x_4256_);
    return v___x_4257_;
}
pub unsafe fn l_Lean_MVarId_checkNotAssigned(
    mut v_mvarId_4258_: *mut LeanObject,
    mut v_tacticName_4259_: *mut LeanObject,
    mut v_a_4260_: *mut LeanObject,
    mut v_a_4261_: *mut LeanObject,
    mut v_a_4262_: *mut LeanObject,
    mut v_a_4263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4269_: u8 = 0;
    let mut v___x_4270_: u8 = 0;
    let mut v___x_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4277_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4265_ =
                    l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(
                        v_mvarId_4258_,
                        v_a_4261_,
                    );
                v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
                v_isSharedCheck_4277_ = (!lean_is_exclusive(v___x_4265_)) as u8;
                if v_isSharedCheck_4277_ == 0 {
                    v___x_4268_ = v___x_4265_;
                    v_isShared_4269_ = v_isSharedCheck_4277_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_4266_);
                    lean_dec(v___x_4265_);
                    v___x_4268_ = lean_box(0);
                    v_isShared_4269_ = v_isSharedCheck_4277_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4270_ = (lean_unbox(v_a_4266_) as u8);
                lean_dec(v_a_4266_);
                if v___x_4270_ == 0 {
                    lean_dec(v_tacticName_4259_);
                    lean_dec(v_mvarId_4258_);
                    v___x_4271_ = lean_box(0);
                    if v_isShared_4269_ == 0 {
                        lean_ctor_set(v___x_4268_, 0, v___x_4271_);
                        v___x_4273_ = v___x_4268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4274_, 0, v___x_4271_);
                        v___x_4273_ = v_reuseFailAlloc_4274_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4268_);
                    v___x_4275_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__7),
                        core::ptr::addr_of_mut!(l_Lean_MVarId_checkNotAssigned___closed__7_once),
                        _init_l_Lean_MVarId_checkNotAssigned___closed__7,
                    );
                    v___x_4276_ = l_Lean_Meta_throwTacticEx___redArg(
                        v_tacticName_4259_,
                        v_mvarId_4258_,
                        v___x_4275_,
                        v_a_4260_,
                        v_a_4261_,
                        v_a_4262_,
                        v_a_4263_,
                    );
                    return v___x_4276_;
                }
            }
            2 => {
                return v___x_4273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_checkNotAssigned___boxed(
    mut v_mvarId_4278_: *mut LeanObject,
    mut v_tacticName_4279_: *mut LeanObject,
    mut v_a_4280_: *mut LeanObject,
    mut v_a_4281_: *mut LeanObject,
    mut v_a_4282_: *mut LeanObject,
    mut v_a_4283_: *mut LeanObject,
    mut v_a_4284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4285_: *mut LeanObject = core::ptr::null_mut();
    v_res_4285_ = l_Lean_MVarId_checkNotAssigned(
        v_mvarId_4278_,
        v_tacticName_4279_,
        v_a_4280_,
        v_a_4281_,
        v_a_4282_,
        v_a_4283_,
    );
    lean_dec(v_a_4283_);
    lean_dec_ref(v_a_4282_);
    lean_dec(v_a_4281_);
    lean_dec_ref(v_a_4280_);
    return v_res_4285_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(
    mut v_mvarId_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4292_: *mut LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___redArg(
        v_mvarId_4286_,
        v___y_4288_,
    );
    return v___x_4292_;
}
pub unsafe fn l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0___boxed(
    mut v_mvarId_4293_: *mut LeanObject,
    mut v___y_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4299_: *mut LeanObject = core::ptr::null_mut();
    v_res_4299_ = l_Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0(
        v_mvarId_4293_,
        v___y_4294_,
        v___y_4295_,
        v___y_4296_,
        v___y_4297_,
    );
    lean_dec(v___y_4297_);
    lean_dec_ref(v___y_4296_);
    lean_dec(v___y_4295_);
    lean_dec_ref(v___y_4294_);
    lean_dec(v_mvarId_4293_);
    return v_res_4299_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(
    mut v_00_u03b2_4300_: *mut LeanObject,
    mut v_x_4301_: *mut LeanObject,
    mut v_x_4302_: *mut LeanObject,
) -> u8 {
    let mut v___x_4303_: u8 = 0;
    v___x_4303_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___redArg(v_x_4301_, v_x_4302_);
    return v___x_4303_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0___boxed(
    mut v_00_u03b2_4304_: *mut LeanObject,
    mut v_x_4305_: *mut LeanObject,
    mut v_x_4306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4307_: u8 = 0;
    let mut v_r_4308_: *mut LeanObject = core::ptr::null_mut();
    v_res_4307_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0(v_00_u03b2_4304_, v_x_4305_, v_x_4306_);
    lean_dec(v_x_4306_);
    lean_dec_ref(v_x_4305_);
    v_r_4308_ = lean_box((v_res_4307_) as usize);
    return v_r_4308_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(
    mut v_00_u03b2_4309_: *mut LeanObject,
    mut v_x_4310_: *mut LeanObject,
    mut v_x_4311_: usize,
    mut v_x_4312_: *mut LeanObject,
) -> u8 {
    let mut v___x_4313_: u8 = 0;
    v___x_4313_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg(v_x_4310_, v_x_4311_, v_x_4312_);
    return v___x_4313_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_4314_: *mut LeanObject,
    mut v_x_4315_: *mut LeanObject,
    mut v_x_4316_: *mut LeanObject,
    mut v_x_4317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_769__boxed_4318_: usize = 0;
    let mut v_res_4319_: u8 = 0;
    let mut v_r_4320_: *mut LeanObject = core::ptr::null_mut();
    v_x_769__boxed_4318_ = lean_unbox_usize(v_x_4316_);
    lean_dec(v_x_4316_);
    v_res_4319_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1(v_00_u03b2_4314_, v_x_4315_, v_x_769__boxed_4318_, v_x_4317_);
    lean_dec(v_x_4317_);
    lean_dec_ref(v_x_4315_);
    v_r_4320_ = lean_box((v_res_4319_) as usize);
    return v_r_4320_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4321_: *mut LeanObject,
    mut v_keys_4322_: *mut LeanObject,
    mut v_vals_4323_: *mut LeanObject,
    mut v_heq_4324_: *mut LeanObject,
    mut v_i_4325_: *mut LeanObject,
    mut v_k_4326_: *mut LeanObject,
) -> u8 {
    let mut v___x_4327_: u8 = 0;
    v___x_4327_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4322_, v_i_4325_, v_k_4326_);
    return v___x_4327_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2___boxed(
    mut v_00_u03b2_4328_: *mut LeanObject,
    mut v_keys_4329_: *mut LeanObject,
    mut v_vals_4330_: *mut LeanObject,
    mut v_heq_4331_: *mut LeanObject,
    mut v_i_4332_: *mut LeanObject,
    mut v_k_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4334_: u8 = 0;
    let mut v_r_4335_: *mut LeanObject = core::ptr::null_mut();
    v_res_4334_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1_spec__2(v_00_u03b2_4328_, v_keys_4329_, v_vals_4330_, v_heq_4331_, v_i_4332_, v_k_4333_);
    lean_dec(v_k_4333_);
    lean_dec_ref(v_vals_4330_);
    lean_dec_ref(v_keys_4329_);
    v_r_4335_ = lean_box((v_res_4334_) as usize);
    return v_r_4335_;
}
pub unsafe fn l_Lean_MVarId_getType(
    mut v_mvarId_4336_: *mut LeanObject,
    mut v_a_4337_: *mut LeanObject,
    mut v_a_4338_: *mut LeanObject,
    mut v_a_4339_: *mut LeanObject,
    mut v_a_4340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4346_: u8 = 0;
    let mut v_type_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4351_: u8 = 0;
    let mut v_a_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4355_: u8 = 0;
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4359_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4342_ = l_Lean_MVarId_getDecl(
                    v_mvarId_4336_,
                    v_a_4337_,
                    v_a_4338_,
                    v_a_4339_,
                    v_a_4340_,
                );
                if lean_obj_tag(v___x_4342_) == 0 {
                    v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
                    v_isSharedCheck_4351_ = (!lean_is_exclusive(v___x_4342_)) as u8;
                    if v_isSharedCheck_4351_ == 0 {
                        v___x_4345_ = v___x_4342_;
                        v_isShared_4346_ = v_isSharedCheck_4351_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4343_);
                        lean_dec(v___x_4342_);
                        v___x_4345_ = lean_box(0);
                        v_isShared_4346_ = v_isSharedCheck_4351_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4352_ = lean_ctor_get(v___x_4342_, 0);
                    v_isSharedCheck_4359_ = (!lean_is_exclusive(v___x_4342_)) as u8;
                    if v_isSharedCheck_4359_ == 0 {
                        v___x_4354_ = v___x_4342_;
                        v_isShared_4355_ = v_isSharedCheck_4359_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4352_);
                        lean_dec(v___x_4342_);
                        v___x_4354_ = lean_box(0);
                        v_isShared_4355_ = v_isSharedCheck_4359_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_type_4347_ = lean_ctor_get(v_a_4343_, 2);
                lean_inc_ref(v_type_4347_);
                lean_dec(v_a_4343_);
                if v_isShared_4346_ == 0 {
                    lean_ctor_set(v___x_4345_, 0, v_type_4347_);
                    v___x_4349_ = v___x_4345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4350_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4350_, 0, v_type_4347_);
                    v___x_4349_ = v_reuseFailAlloc_4350_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4349_;
            }
            3 => {
                if v_isShared_4355_ == 0 {
                    v___x_4357_ = v___x_4354_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4358_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4358_, 0, v_a_4352_);
                    v___x_4357_ = v_reuseFailAlloc_4358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4357_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_getType___boxed(
    mut v_mvarId_4360_: *mut LeanObject,
    mut v_a_4361_: *mut LeanObject,
    mut v_a_4362_: *mut LeanObject,
    mut v_a_4363_: *mut LeanObject,
    mut v_a_4364_: *mut LeanObject,
    mut v_a_4365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4366_: *mut LeanObject = core::ptr::null_mut();
    v_res_4366_ = l_Lean_MVarId_getType(v_mvarId_4360_, v_a_4361_, v_a_4362_, v_a_4363_, v_a_4364_);
    lean_dec(v_a_4364_);
    lean_dec_ref(v_a_4363_);
    lean_dec(v_a_4362_);
    lean_dec_ref(v_a_4361_);
    return v_res_4366_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
    mut v_e_4367_: *mut LeanObject,
    mut v___y_4368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4370_: u8 = 0;
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4390_: u8 = 0;
    let mut v_unused_4391_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4370_ = l_Lean_Expr_hasMVar(v_e_4367_);
                if v___x_4370_ == 0 {
                    v___x_4371_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4371_, 0, v_e_4367_);
                    return v___x_4371_;
                } else {
                    v___x_4372_ = lean_st_ref_get(v___y_4368_);
                    v_mctx_4373_ = lean_ctor_get(v___x_4372_, 0);
                    lean_inc_ref(v_mctx_4373_);
                    lean_dec(v___x_4372_);
                    v___x_4374_ = l_Lean_instantiateMVarsCore(v_mctx_4373_, v_e_4367_);
                    v_fst_4375_ = lean_ctor_get(v___x_4374_, 0);
                    lean_inc(v_fst_4375_);
                    v_snd_4376_ = lean_ctor_get(v___x_4374_, 1);
                    lean_inc(v_snd_4376_);
                    lean_dec_ref(v___x_4374_);
                    v___x_4377_ = lean_st_ref_take(v___y_4368_);
                    v_cache_4378_ = lean_ctor_get(v___x_4377_, 1);
                    v_zetaDeltaFVarIds_4379_ = lean_ctor_get(v___x_4377_, 2);
                    v_postponed_4380_ = lean_ctor_get(v___x_4377_, 3);
                    v_diag_4381_ = lean_ctor_get(v___x_4377_, 4);
                    v_isSharedCheck_4390_ = (!lean_is_exclusive(v___x_4377_)) as u8;
                    if v_isSharedCheck_4390_ == 0 {
                        v_unused_4391_ = lean_ctor_get(v___x_4377_, 0);
                        lean_dec(v_unused_4391_);
                        v___x_4383_ = v___x_4377_;
                        v_isShared_4384_ = v_isSharedCheck_4390_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_4381_);
                        lean_inc(v_postponed_4380_);
                        lean_inc(v_zetaDeltaFVarIds_4379_);
                        lean_inc(v_cache_4378_);
                        lean_dec(v___x_4377_);
                        v___x_4383_ = lean_box(0);
                        v_isShared_4384_ = v_isSharedCheck_4390_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4384_ == 0 {
                    lean_ctor_set(v___x_4383_, 0, v_snd_4376_);
                    v___x_4386_ = v___x_4383_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_snd_4376_);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 1, v_cache_4378_);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 2, v_zetaDeltaFVarIds_4379_);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 3, v_postponed_4380_);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 4, v_diag_4381_);
                    v___x_4386_ = v_reuseFailAlloc_4389_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4387_ = lean_st_ref_set(v___y_4368_, v___x_4386_);
                v___x_4388_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4388_, 0, v_fst_4375_);
                return v___x_4388_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg___boxed(
    mut v_e_4392_: *mut LeanObject,
    mut v___y_4393_: *mut LeanObject,
    mut v___y_4394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4395_: *mut LeanObject = core::ptr::null_mut();
    v_res_4395_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
        v_e_4392_,
        v___y_4393_,
    );
    lean_dec(v___y_4393_);
    return v_res_4395_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(
    mut v_e_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4402_: *mut LeanObject = core::ptr::null_mut();
    v___x_4402_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
        v_e_4396_,
        v___y_4398_,
    );
    return v___x_4402_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___boxed(
    mut v_e_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
    mut v___y_4407_: *mut LeanObject,
    mut v___y_4408_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4409_: *mut LeanObject = core::ptr::null_mut();
    v_res_4409_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0(
        v_e_4403_,
        v___y_4404_,
        v___y_4405_,
        v___y_4406_,
        v___y_4407_,
    );
    lean_dec(v___y_4407_);
    lean_dec_ref(v___y_4406_);
    lean_dec(v___y_4405_);
    lean_dec_ref(v___y_4404_);
    return v_res_4409_;
}
pub unsafe fn l_Lean_MVarId_getType_x27(
    mut v_mvarId_4410_: *mut LeanObject,
    mut v_a_4411_: *mut LeanObject,
    mut v_a_4412_: *mut LeanObject,
    mut v_a_4413_: *mut LeanObject,
    mut v_a_4414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    v___x_4416_ = l_Lean_MVarId_getType(v_mvarId_4410_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
    if lean_obj_tag(v___x_4416_) == 0 {
        let mut v_a_4417_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
        v_a_4417_ = lean_ctor_get(v___x_4416_, 0);
        lean_inc(v_a_4417_);
        lean_dec_ref_known(v___x_4416_, 1);
        lean_inc(v_a_4414_);
        lean_inc_ref(v_a_4413_);
        lean_inc(v_a_4412_);
        lean_inc_ref(v_a_4411_);
        v___x_4418_ = lean_whnf(v_a_4417_, v_a_4411_, v_a_4412_, v_a_4413_, v_a_4414_);
        if lean_obj_tag(v___x_4418_) == 0 {
            let mut v_a_4419_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
            v_a_4419_ = lean_ctor_get(v___x_4418_, 0);
            lean_inc(v_a_4419_);
            lean_dec_ref_known(v___x_4418_, 1);
            v___x_4420_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
                v_a_4419_, v_a_4412_,
            );
            return v___x_4420_;
        } else {
            return v___x_4418_;
        }
    } else {
        return v___x_4416_;
    }
}
pub unsafe fn l_Lean_MVarId_getType_x27___boxed(
    mut v_mvarId_4421_: *mut LeanObject,
    mut v_a_4422_: *mut LeanObject,
    mut v_a_4423_: *mut LeanObject,
    mut v_a_4424_: *mut LeanObject,
    mut v_a_4425_: *mut LeanObject,
    mut v_a_4426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4427_: *mut LeanObject = core::ptr::null_mut();
    v_res_4427_ =
        l_Lean_MVarId_getType_x27(v_mvarId_4421_, v_a_4422_, v_a_4423_, v_a_4424_, v_a_4425_);
    lean_dec(v_a_4425_);
    lean_dec_ref(v_a_4424_);
    lean_dec(v_a_4423_);
    lean_dec_ref(v_a_4422_);
    return v_res_4427_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: u8 = 0;
    let mut v___x_4495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    v___x_4493_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_;
    v___x_4494_ = 0;
    v___x_4495_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__25_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_;
    v___x_4496_ = l_Lean_registerTraceClass(v___x_4493_, v___x_4494_, v___x_4495_);
    return v___x_4496_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2____boxed(
    mut v_a_4497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4498_: *mut LeanObject = core::ptr::null_mut();
    v_res_4498_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
    return v_res_4498_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
    mut v_mvarId_4499_: *mut LeanObject,
    mut v_x_4500_: *mut LeanObject,
    mut v___y_4501_: *mut LeanObject,
    mut v___y_4502_: *mut LeanObject,
    mut v___y_4503_: *mut LeanObject,
    mut v___y_4504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4510_: u8 = 0;
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4514_: u8 = 0;
    let mut v_a_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4518_: u8 = 0;
    let mut v___x_4520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4506_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    lean_box(0),
                    v_mvarId_4499_,
                    v_x_4500_,
                    v___y_4501_,
                    v___y_4502_,
                    v___y_4503_,
                    v___y_4504_,
                );
                if lean_obj_tag(v___x_4506_) == 0 {
                    v_a_4507_ = lean_ctor_get(v___x_4506_, 0);
                    v_isSharedCheck_4514_ = (!lean_is_exclusive(v___x_4506_)) as u8;
                    if v_isSharedCheck_4514_ == 0 {
                        v___x_4509_ = v___x_4506_;
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4507_);
                        lean_dec(v___x_4506_);
                        v___x_4509_ = lean_box(0);
                        v_isShared_4510_ = v_isSharedCheck_4514_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4515_ = lean_ctor_get(v___x_4506_, 0);
                    v_isSharedCheck_4522_ = (!lean_is_exclusive(v___x_4506_)) as u8;
                    if v_isSharedCheck_4522_ == 0 {
                        v___x_4517_ = v___x_4506_;
                        v_isShared_4518_ = v_isSharedCheck_4522_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4515_);
                        lean_dec(v___x_4506_);
                        v___x_4517_ = lean_box(0);
                        v_isShared_4518_ = v_isSharedCheck_4522_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4510_ == 0 {
                    v___x_4512_ = v___x_4509_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4513_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
                    v___x_4512_ = v_reuseFailAlloc_4513_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4512_;
            }
            3 => {
                if v_isShared_4518_ == 0 {
                    v___x_4520_ = v___x_4517_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4521_, 0, v_a_4515_);
                    v___x_4520_ = v_reuseFailAlloc_4521_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4520_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg___boxed(
    mut v_mvarId_4523_: *mut LeanObject,
    mut v_x_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
    mut v___y_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4530_: *mut LeanObject = core::ptr::null_mut();
    v_res_4530_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
        v_mvarId_4523_,
        v_x_4524_,
        v___y_4525_,
        v___y_4526_,
        v___y_4527_,
        v___y_4528_,
    );
    lean_dec(v___y_4528_);
    lean_dec_ref(v___y_4527_);
    lean_dec(v___y_4526_);
    lean_dec_ref(v___y_4525_);
    return v_res_4530_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(
    mut v_00_u03b1_4531_: *mut LeanObject,
    mut v_mvarId_4532_: *mut LeanObject,
    mut v_x_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    v___x_4539_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
        v_mvarId_4532_,
        v_x_4533_,
        v___y_4534_,
        v___y_4535_,
        v___y_4536_,
        v___y_4537_,
    );
    return v___x_4539_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___boxed(
    mut v_00_u03b1_4540_: *mut LeanObject,
    mut v_mvarId_4541_: *mut LeanObject,
    mut v_x_4542_: *mut LeanObject,
    mut v___y_4543_: *mut LeanObject,
    mut v___y_4544_: *mut LeanObject,
    mut v___y_4545_: *mut LeanObject,
    mut v___y_4546_: *mut LeanObject,
    mut v___y_4547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4548_: *mut LeanObject = core::ptr::null_mut();
    v_res_4548_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1(
        v_00_u03b1_4540_,
        v_mvarId_4541_,
        v_x_4542_,
        v___y_4543_,
        v___y_4544_,
        v___y_4545_,
        v___y_4546_,
    );
    lean_dec(v___y_4546_);
    lean_dec_ref(v___y_4545_);
    lean_dec(v___y_4544_);
    lean_dec_ref(v___y_4543_);
    return v_res_4548_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_4549_: *mut LeanObject,
    mut v_x_4550_: *mut LeanObject,
    mut v_x_4551_: *mut LeanObject,
    mut v_x_4552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4557_: u8 = 0;
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4559_: u8 = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4553_ = lean_ctor_get(v_x_4549_, 0);
                v_vs_4554_ = lean_ctor_get(v_x_4549_, 1);
                v_isSharedCheck_4578_ = (!lean_is_exclusive(v_x_4549_)) as u8;
                if v_isSharedCheck_4578_ == 0 {
                    v___x_4556_ = v_x_4549_;
                    v_isShared_4557_ = v_isSharedCheck_4578_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4554_);
                    lean_inc(v_ks_4553_);
                    lean_dec(v_x_4549_);
                    v___x_4556_ = lean_box(0);
                    v_isShared_4557_ = v_isSharedCheck_4578_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4558_ = lean_array_get_size(v_ks_4553_);
                v___x_4559_ = lean_nat_dec_lt(v_x_4550_, v___x_4558_);
                if v___x_4559_ == 0 {
                    lean_dec(v_x_4550_);
                    v___x_4560_ = lean_array_push(v_ks_4553_, v_x_4551_);
                    v___x_4561_ = lean_array_push(v_vs_4554_, v_x_4552_);
                    if v_isShared_4557_ == 0 {
                        lean_ctor_set(v___x_4556_, 1, v___x_4561_);
                        lean_ctor_set(v___x_4556_, 0, v___x_4560_);
                        v___x_4563_ = v___x_4556_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4564_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4560_);
                        lean_ctor_set(v_reuseFailAlloc_4564_, 1, v___x_4561_);
                        v___x_4563_ = v_reuseFailAlloc_4564_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4565_ = lean_array_fget_borrowed(v_ks_4553_, v_x_4550_);
                    v___x_4566_ = l_Lean_instBEqMVarId_beq(v_x_4551_, v_k_x27_4565_);
                    if v___x_4566_ == 0 {
                        if v_isShared_4557_ == 0 {
                            v___x_4568_ = v___x_4556_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_ks_4553_);
                            lean_ctor_set(v_reuseFailAlloc_4572_, 1, v_vs_4554_);
                            v___x_4568_ = v_reuseFailAlloc_4572_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4573_ = lean_array_fset(v_ks_4553_, v_x_4550_, v_x_4551_);
                        v___x_4574_ = lean_array_fset(v_vs_4554_, v_x_4550_, v_x_4552_);
                        lean_dec(v_x_4550_);
                        if v_isShared_4557_ == 0 {
                            lean_ctor_set(v___x_4556_, 1, v___x_4574_);
                            lean_ctor_set(v___x_4556_, 0, v___x_4573_);
                            v___x_4576_ = v___x_4556_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4577_, 0, v___x_4573_);
                            lean_ctor_set(v_reuseFailAlloc_4577_, 1, v___x_4574_);
                            v___x_4576_ = v_reuseFailAlloc_4577_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4563_;
            }
            3 => {
                v___x_4569_ = lean_unsigned_to_nat(1);
                v___x_4570_ = lean_nat_add(v_x_4550_, v___x_4569_);
                lean_dec(v_x_4550_);
                v_x_4549_ = v___x_4568_;
                v_x_4550_ = v___x_4570_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_4579_: *mut LeanObject,
    mut v_k_4580_: *mut LeanObject,
    mut v_v_4581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4583_: *mut LeanObject = core::ptr::null_mut();
    v___x_4582_ = lean_unsigned_to_nat(0);
    v___x_4583_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_4579_, v___x_4582_, v_k_4580_, v_v_4581_);
    return v___x_4583_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    v___x_4584_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4584_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(
    mut v_x_4585_: *mut LeanObject,
    mut v_x_4586_: usize,
    mut v_x_4587_: usize,
    mut v_x_4588_: *mut LeanObject,
    mut v_x_4589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4591_: usize = 0;
    let mut v___x_4592_: usize = 0;
    let mut v___x_4593_: usize = 0;
    let mut v___x_4594_: usize = 0;
    let mut v_j_4595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4597_: u8 = 0;
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4600_: u8 = 0;
    let mut v_v_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4610_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4614_: u8 = 0;
    let mut v___x_4615_: u8 = 0;
    let mut v___x_4616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4621_: u8 = 0;
    let mut v_node_4622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4625_: u8 = 0;
    let mut v___x_4626_: usize = 0;
    let mut v___x_4627_: usize = 0;
    let mut v___x_4628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4632_: u8 = 0;
    let mut v___x_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4634_: u8 = 0;
    let mut v_unused_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4640_: u8 = 0;
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4645_: u8 = 0;
    let mut v_ks_4646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: usize = 0;
    let mut v___x_4652_: u8 = 0;
    let mut v___x_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4655_: u8 = 0;
    let mut v_reuseFailAlloc_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4585_) == 0 {
                    v_es_4590_ = lean_ctor_get(v_x_4585_, 0);
                    v___x_4591_ = 5usize;
                    v___x_4592_ = 1usize;
                    v___x_4593_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_MVarId_checkNotAssigned_spec__0_spec__0_spec__1___redArg___closed__1);
                    v___x_4594_ = lean_usize_land(v_x_4586_, v___x_4593_);
                    v_j_4595_ = lean_usize_to_nat(v___x_4594_);
                    v___x_4596_ = lean_array_get_size(v_es_4590_);
                    v___x_4597_ = lean_nat_dec_lt(v_j_4595_, v___x_4596_);
                    if v___x_4597_ == 0 {
                        lean_dec(v_j_4595_);
                        lean_dec(v_x_4589_);
                        lean_dec(v_x_4588_);
                        return v_x_4585_;
                    } else {
                        lean_inc_ref(v_es_4590_);
                        v_isSharedCheck_4634_ = (!lean_is_exclusive(v_x_4585_)) as u8;
                        if v_isSharedCheck_4634_ == 0 {
                            v_unused_4635_ = lean_ctor_get(v_x_4585_, 0);
                            lean_dec(v_unused_4635_);
                            v___x_4599_ = v_x_4585_;
                            v_isShared_4600_ = v_isSharedCheck_4634_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4585_);
                            v___x_4599_ = lean_box(0);
                            v_isShared_4600_ = v_isSharedCheck_4634_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4636_ = lean_ctor_get(v_x_4585_, 0);
                    v_vs_4637_ = lean_ctor_get(v_x_4585_, 1);
                    v_isSharedCheck_4657_ = (!lean_is_exclusive(v_x_4585_)) as u8;
                    if v_isSharedCheck_4657_ == 0 {
                        v___x_4639_ = v_x_4585_;
                        v_isShared_4640_ = v_isSharedCheck_4657_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4637_);
                        lean_inc(v_ks_4636_);
                        lean_dec(v_x_4585_);
                        v___x_4639_ = lean_box(0);
                        v_isShared_4640_ = v_isSharedCheck_4657_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4601_ = lean_array_fget(v_es_4590_, v_j_4595_);
                v___x_4602_ = lean_box(0);
                v_xs_x27_4603_ = lean_array_fset(v_es_4590_, v_j_4595_, v___x_4602_);
                match lean_obj_tag(v_v_4601_) {
                    0 => {
                        v_key_4610_ = lean_ctor_get(v_v_4601_, 0);
                        v_val_4611_ = lean_ctor_get(v_v_4601_, 1);
                        v_isSharedCheck_4621_ = (!lean_is_exclusive(v_v_4601_)) as u8;
                        if v_isSharedCheck_4621_ == 0 {
                            v___x_4613_ = v_v_4601_;
                            v_isShared_4614_ = v_isSharedCheck_4621_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4611_);
                            lean_inc(v_key_4610_);
                            lean_dec(v_v_4601_);
                            v___x_4613_ = lean_box(0);
                            v_isShared_4614_ = v_isSharedCheck_4621_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4622_ = lean_ctor_get(v_v_4601_, 0);
                        v_isSharedCheck_4632_ = (!lean_is_exclusive(v_v_4601_)) as u8;
                        if v_isSharedCheck_4632_ == 0 {
                            v___x_4624_ = v_v_4601_;
                            v_isShared_4625_ = v_isSharedCheck_4632_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4622_);
                            lean_dec(v_v_4601_);
                            v___x_4624_ = lean_box(0);
                            v_isShared_4625_ = v_isSharedCheck_4632_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4633_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4633_, 0, v_x_4588_);
                        lean_ctor_set(v___x_4633_, 1, v_x_4589_);
                        v___y_4605_ = v___x_4633_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4606_ = lean_array_fset(v_xs_x27_4603_, v_j_4595_, v___y_4605_);
                lean_dec(v_j_4595_);
                if v_isShared_4600_ == 0 {
                    lean_ctor_set(v___x_4599_, 0, v___x_4606_);
                    v___x_4608_ = v___x_4599_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
                    v___x_4608_ = v_reuseFailAlloc_4609_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4608_;
            }
            4 => {
                v___x_4615_ = l_Lean_instBEqMVarId_beq(v_x_4588_, v_key_4610_);
                if v___x_4615_ == 0 {
                    lean_del_object(v___x_4613_);
                    v___x_4616_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4610_,
                        v_val_4611_,
                        v_x_4588_,
                        v_x_4589_,
                    );
                    v___x_4617_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4617_, 0, v___x_4616_);
                    v___y_4605_ = v___x_4617_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4611_);
                    lean_dec(v_key_4610_);
                    if v_isShared_4614_ == 0 {
                        lean_ctor_set(v___x_4613_, 1, v_x_4589_);
                        lean_ctor_set(v___x_4613_, 0, v_x_4588_);
                        v___x_4619_ = v___x_4613_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4620_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4620_, 0, v_x_4588_);
                        lean_ctor_set(v_reuseFailAlloc_4620_, 1, v_x_4589_);
                        v___x_4619_ = v_reuseFailAlloc_4620_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4605_ = v___x_4619_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4626_ = lean_usize_shift_right(v_x_4586_, v___x_4591_);
                v___x_4627_ = lean_usize_add(v_x_4587_, v___x_4592_);
                v___x_4628_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_node_4622_, v___x_4626_, v___x_4627_, v_x_4588_, v_x_4589_);
                if v_isShared_4625_ == 0 {
                    lean_ctor_set(v___x_4624_, 0, v___x_4628_);
                    v___x_4630_ = v___x_4624_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4631_, 0, v___x_4628_);
                    v___x_4630_ = v_reuseFailAlloc_4631_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4605_ = v___x_4630_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4640_ == 0 {
                    v___x_4642_ = v___x_4639_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4656_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4656_, 0, v_ks_4636_);
                    lean_ctor_set(v_reuseFailAlloc_4656_, 1, v_vs_4637_);
                    v___x_4642_ = v_reuseFailAlloc_4656_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4643_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v___x_4642_, v_x_4588_, v_x_4589_);
                v___x_4651_ = 7usize;
                v___x_4652_ = lean_usize_dec_le(v___x_4651_, v_x_4587_);
                if v___x_4652_ == 0 {
                    v___x_4653_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4643_);
                    v___x_4654_ = lean_unsigned_to_nat(4);
                    v___x_4655_ = lean_nat_dec_lt(v___x_4653_, v___x_4654_);
                    lean_dec(v___x_4653_);
                    v___y_4645_ = v___x_4655_;
                    state = 10;
                    continue;
                } else {
                    v___y_4645_ = v___x_4652_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4645_ == 0 {
                    v_ks_4646_ = lean_ctor_get(v_newNode_4643_, 0);
                    lean_inc_ref(v_ks_4646_);
                    v_vs_4647_ = lean_ctor_get(v_newNode_4643_, 1);
                    lean_inc_ref(v_vs_4647_);
                    lean_dec_ref(v_newNode_4643_);
                    v___x_4648_ = lean_unsigned_to_nat(0);
                    v___x_4649_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___x_4650_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_x_4587_, v_ks_4646_, v_vs_4647_, v___x_4648_, v___x_4649_);
                    lean_dec_ref(v_vs_4647_);
                    lean_dec_ref(v_ks_4646_);
                    return v___x_4650_;
                } else {
                    return v_newNode_4643_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_4658_: usize,
    mut v_keys_4659_: *mut LeanObject,
    mut v_vals_4660_: *mut LeanObject,
    mut v_i_4661_: *mut LeanObject,
    mut v_entries_4662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: u8 = 0;
    let mut v_k_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: u64 = 0;
    let mut v_h_4668_: usize = 0;
    let mut v___x_4669_: usize = 0;
    let mut v___x_4670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4671_: usize = 0;
    let mut v___x_4672_: usize = 0;
    let mut v___x_4673_: usize = 0;
    let mut v_h_4674_: usize = 0;
    let mut v___x_4675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4676_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4663_ = lean_array_get_size(v_keys_4659_);
                v___x_4664_ = lean_nat_dec_lt(v_i_4661_, v___x_4663_);
                if v___x_4664_ == 0 {
                    lean_dec(v_i_4661_);
                    return v_entries_4662_;
                } else {
                    v_k_4665_ = lean_array_fget_borrowed(v_keys_4659_, v_i_4661_);
                    v_v_4666_ = lean_array_fget_borrowed(v_vals_4660_, v_i_4661_);
                    v___x_4667_ = l_Lean_instHashableMVarId_hash(v_k_4665_);
                    v_h_4668_ = lean_uint64_to_usize(v___x_4667_);
                    v___x_4669_ = 5usize;
                    v___x_4670_ = lean_unsigned_to_nat(1);
                    v___x_4671_ = 1usize;
                    v___x_4672_ = lean_usize_sub(v_depth_4658_, v___x_4671_);
                    v___x_4673_ = lean_usize_mul(v___x_4669_, v___x_4672_);
                    v_h_4674_ = lean_usize_shift_right(v_h_4668_, v___x_4673_);
                    v___x_4675_ = lean_nat_add(v_i_4661_, v___x_4670_);
                    lean_dec(v_i_4661_);
                    lean_inc(v_v_4666_);
                    lean_inc(v_k_4665_);
                    v___x_4676_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_entries_4662_, v_h_4674_, v_depth_4658_, v_k_4665_, v_v_4666_);
                    v_i_4661_ = v___x_4675_;
                    v_entries_4662_ = v___x_4676_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_4678_: *mut LeanObject,
    mut v_keys_4679_: *mut LeanObject,
    mut v_vals_4680_: *mut LeanObject,
    mut v_i_4681_: *mut LeanObject,
    mut v_entries_4682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4683_: usize = 0;
    let mut v_res_4684_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4683_ = lean_unbox_usize(v_depth_4678_);
    lean_dec(v_depth_4678_);
    v_res_4684_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_4683_, v_keys_4679_, v_vals_4680_, v_i_4681_, v_entries_4682_);
    lean_dec_ref(v_vals_4680_);
    lean_dec_ref(v_keys_4679_);
    return v_res_4684_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_4685_: *mut LeanObject,
    mut v_x_4686_: *mut LeanObject,
    mut v_x_4687_: *mut LeanObject,
    mut v_x_4688_: *mut LeanObject,
    mut v_x_4689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1015__boxed_4690_: usize = 0;
    let mut v_x_1016__boxed_4691_: usize = 0;
    let mut v_res_4692_: *mut LeanObject = core::ptr::null_mut();
    v_x_1015__boxed_4690_ = lean_unbox_usize(v_x_4686_);
    lean_dec(v_x_4686_);
    v_x_1016__boxed_4691_ = lean_unbox_usize(v_x_4687_);
    lean_dec(v_x_4687_);
    v_res_4692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_4685_, v_x_1015__boxed_4690_, v_x_1016__boxed_4691_, v_x_4688_, v_x_4689_);
    return v_res_4692_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(
    mut v_x_4693_: *mut LeanObject,
    mut v_x_4694_: *mut LeanObject,
    mut v_x_4695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4696_: u64 = 0;
    let mut v___x_4697_: usize = 0;
    let mut v___x_4698_: usize = 0;
    let mut v___x_4699_: *mut LeanObject = core::ptr::null_mut();
    v___x_4696_ = l_Lean_instHashableMVarId_hash(v_x_4694_);
    v___x_4697_ = lean_uint64_to_usize(v___x_4696_);
    v___x_4698_ = 1usize;
    v___x_4699_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_4693_, v___x_4697_, v___x_4698_, v_x_4694_, v_x_4695_);
    return v___x_4699_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
    mut v_mvarId_4700_: *mut LeanObject,
    mut v_val_4701_: *mut LeanObject,
    mut v___y_4702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_4708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_4709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4712_: u8 = 0;
    let mut v_depth_4713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_4714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_4715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lDecls_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_userNames_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_4720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4725_: u8 = 0;
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4736_: u8 = 0;
    let mut v_isSharedCheck_4737_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4704_ = lean_st_ref_take(v___y_4702_);
                v_mctx_4705_ = lean_ctor_get(v___x_4704_, 0);
                v_cache_4706_ = lean_ctor_get(v___x_4704_, 1);
                v_zetaDeltaFVarIds_4707_ = lean_ctor_get(v___x_4704_, 2);
                v_postponed_4708_ = lean_ctor_get(v___x_4704_, 3);
                v_diag_4709_ = lean_ctor_get(v___x_4704_, 4);
                v_isSharedCheck_4737_ = (!lean_is_exclusive(v___x_4704_)) as u8;
                if v_isSharedCheck_4737_ == 0 {
                    v___x_4711_ = v___x_4704_;
                    v_isShared_4712_ = v_isSharedCheck_4737_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_diag_4709_);
                    lean_inc(v_postponed_4708_);
                    lean_inc(v_zetaDeltaFVarIds_4707_);
                    lean_inc(v_cache_4706_);
                    lean_inc(v_mctx_4705_);
                    lean_dec(v___x_4704_);
                    v___x_4711_ = lean_box(0);
                    v_isShared_4712_ = v_isSharedCheck_4737_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_4713_ = lean_ctor_get(v_mctx_4705_, 0);
                v_levelAssignDepth_4714_ = lean_ctor_get(v_mctx_4705_, 1);
                v_lmvarCounter_4715_ = lean_ctor_get(v_mctx_4705_, 2);
                v_mvarCounter_4716_ = lean_ctor_get(v_mctx_4705_, 3);
                v_lDecls_4717_ = lean_ctor_get(v_mctx_4705_, 4);
                v_decls_4718_ = lean_ctor_get(v_mctx_4705_, 5);
                v_userNames_4719_ = lean_ctor_get(v_mctx_4705_, 6);
                v_lAssignment_4720_ = lean_ctor_get(v_mctx_4705_, 7);
                v_eAssignment_4721_ = lean_ctor_get(v_mctx_4705_, 8);
                v_dAssignment_4722_ = lean_ctor_get(v_mctx_4705_, 9);
                v_isSharedCheck_4736_ = (!lean_is_exclusive(v_mctx_4705_)) as u8;
                if v_isSharedCheck_4736_ == 0 {
                    v___x_4724_ = v_mctx_4705_;
                    v_isShared_4725_ = v_isSharedCheck_4736_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_dAssignment_4722_);
                    lean_inc(v_eAssignment_4721_);
                    lean_inc(v_lAssignment_4720_);
                    lean_inc(v_userNames_4719_);
                    lean_inc(v_decls_4718_);
                    lean_inc(v_lDecls_4717_);
                    lean_inc(v_mvarCounter_4716_);
                    lean_inc(v_lmvarCounter_4715_);
                    lean_inc(v_levelAssignDepth_4714_);
                    lean_inc(v_depth_4713_);
                    lean_dec(v_mctx_4705_);
                    v___x_4724_ = lean_box(0);
                    v_isShared_4725_ = v_isSharedCheck_4736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4726_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_eAssignment_4721_, v_mvarId_4700_, v_val_4701_);
                if v_isShared_4725_ == 0 {
                    lean_ctor_set(v___x_4724_, 8, v___x_4726_);
                    v___x_4728_ = v___x_4724_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4735_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_depth_4713_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 1, v_levelAssignDepth_4714_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 2, v_lmvarCounter_4715_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 3, v_mvarCounter_4716_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 4, v_lDecls_4717_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 5, v_decls_4718_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 6, v_userNames_4719_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 7, v_lAssignment_4720_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 8, v___x_4726_);
                    lean_ctor_set(v_reuseFailAlloc_4735_, 9, v_dAssignment_4722_);
                    v___x_4728_ = v_reuseFailAlloc_4735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4712_ == 0 {
                    lean_ctor_set(v___x_4711_, 0, v___x_4728_);
                    v___x_4730_ = v___x_4711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 0, v___x_4728_);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 1, v_cache_4706_);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 2, v_zetaDeltaFVarIds_4707_);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 3, v_postponed_4708_);
                    lean_ctor_set(v_reuseFailAlloc_4734_, 4, v_diag_4709_);
                    v___x_4730_ = v_reuseFailAlloc_4734_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4731_ = lean_st_ref_set(v___y_4702_, v___x_4730_);
                v___x_4732_ = lean_box(0);
                v___x_4733_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4733_, 0, v___x_4732_);
                return v___x_4733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg___boxed(
    mut v_mvarId_4738_: *mut LeanObject,
    mut v_val_4739_: *mut LeanObject,
    mut v___y_4740_: *mut LeanObject,
    mut v___y_4741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4742_: *mut LeanObject = core::ptr::null_mut();
    v_res_4742_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
        v_mvarId_4738_,
        v_val_4739_,
        v___y_4740_,
    );
    lean_dec(v___y_4740_);
    return v_res_4742_;
}
pub unsafe fn l_Lean_MVarId_admit___lam__0(
    mut v_mvarId_4743_: *mut LeanObject,
    mut v___x_4744_: *mut LeanObject,
    mut v_synthetic_4745_: u8,
    mut v___y_4746_: *mut LeanObject,
    mut v___y_4747_: *mut LeanObject,
    mut v___y_4748_: *mut LeanObject,
    mut v___y_4749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4754_: u8 = 0;
    let mut v___x_4755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4761_: u8 = 0;
    let mut v___x_4763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4765_: u8 = 0;
    let mut v_a_4766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4769_: u8 = 0;
    let mut v___x_4771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4773_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_4743_);
                v___x_4751_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_4743_,
                    v___x_4744_,
                    v___y_4746_,
                    v___y_4747_,
                    v___y_4748_,
                    v___y_4749_,
                );
                if lean_obj_tag(v___x_4751_) == 0 {
                    lean_dec_ref_known(v___x_4751_, 1);
                    lean_inc(v_mvarId_4743_);
                    v___x_4752_ = l_Lean_MVarId_getType(
                        v_mvarId_4743_,
                        v___y_4746_,
                        v___y_4747_,
                        v___y_4748_,
                        v___y_4749_,
                    );
                    if lean_obj_tag(v___x_4752_) == 0 {
                        v_a_4753_ = lean_ctor_get(v___x_4752_, 0);
                        lean_inc(v_a_4753_);
                        lean_dec_ref_known(v___x_4752_, 1);
                        v___x_4754_ = 1;
                        v___x_4755_ = l_Lean_Meta_mkLabeledSorry(
                            v_a_4753_,
                            v_synthetic_4745_,
                            v___x_4754_,
                            v___y_4746_,
                            v___y_4747_,
                            v___y_4748_,
                            v___y_4749_,
                        );
                        if lean_obj_tag(v___x_4755_) == 0 {
                            v_a_4756_ = lean_ctor_get(v___x_4755_, 0);
                            lean_inc(v_a_4756_);
                            lean_dec_ref_known(v___x_4755_, 1);
                            v___x_4757_ =
                                l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
                                    v_mvarId_4743_,
                                    v_a_4756_,
                                    v___y_4747_,
                                );
                            return v___x_4757_;
                        } else {
                            lean_dec(v_mvarId_4743_);
                            v_a_4758_ = lean_ctor_get(v___x_4755_, 0);
                            v_isSharedCheck_4765_ = (!lean_is_exclusive(v___x_4755_)) as u8;
                            if v_isSharedCheck_4765_ == 0 {
                                v___x_4760_ = v___x_4755_;
                                v_isShared_4761_ = v_isSharedCheck_4765_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_4758_);
                                lean_dec(v___x_4755_);
                                v___x_4760_ = lean_box(0);
                                v_isShared_4761_ = v_isSharedCheck_4765_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_mvarId_4743_);
                        v_a_4766_ = lean_ctor_get(v___x_4752_, 0);
                        v_isSharedCheck_4773_ = (!lean_is_exclusive(v___x_4752_)) as u8;
                        if v_isSharedCheck_4773_ == 0 {
                            v___x_4768_ = v___x_4752_;
                            v_isShared_4769_ = v_isSharedCheck_4773_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4766_);
                            lean_dec(v___x_4752_);
                            v___x_4768_ = lean_box(0);
                            v_isShared_4769_ = v_isSharedCheck_4773_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_mvarId_4743_);
                    return v___x_4751_;
                }
            }
            1 => {
                if v_isShared_4761_ == 0 {
                    v___x_4763_ = v___x_4760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4758_);
                    v___x_4763_ = v_reuseFailAlloc_4764_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4763_;
            }
            3 => {
                if v_isShared_4769_ == 0 {
                    v___x_4771_ = v___x_4768_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
                    v___x_4771_ = v_reuseFailAlloc_4772_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4771_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_admit___lam__0___boxed(
    mut v_mvarId_4774_: *mut LeanObject,
    mut v___x_4775_: *mut LeanObject,
    mut v_synthetic_4776_: *mut LeanObject,
    mut v___y_4777_: *mut LeanObject,
    mut v___y_4778_: *mut LeanObject,
    mut v___y_4779_: *mut LeanObject,
    mut v___y_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthetic_boxed_4782_: u8 = 0;
    let mut v_res_4783_: *mut LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_4782_ = (lean_unbox(v_synthetic_4776_) as u8);
    v_res_4783_ = l_Lean_MVarId_admit___lam__0(
        v_mvarId_4774_,
        v___x_4775_,
        v_synthetic_boxed_4782_,
        v___y_4777_,
        v___y_4778_,
        v___y_4779_,
        v___y_4780_,
    );
    lean_dec(v___y_4780_);
    lean_dec_ref(v___y_4779_);
    lean_dec(v___y_4778_);
    lean_dec_ref(v___y_4777_);
    return v_res_4783_;
}
pub unsafe fn l_Lean_MVarId_admit(
    mut v_mvarId_4787_: *mut LeanObject,
    mut v_synthetic_4788_: u8,
    mut v_a_4789_: *mut LeanObject,
    mut v_a_4790_: *mut LeanObject,
    mut v_a_4791_: *mut LeanObject,
    mut v_a_4792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    v___x_4794_ = l_Lean_MVarId_admit___closed__1;
    v___x_4795_ = lean_box((v_synthetic_4788_) as usize);
    lean_inc(v_mvarId_4787_);
    v___f_4796_ = lean_alloc_closure(
        l_Lean_MVarId_admit___lam__0___boxed as *mut core::ffi::c_void,
        8,
        3,
    );
    lean_closure_set(v___f_4796_, 0, v_mvarId_4787_);
    lean_closure_set(v___f_4796_, 1, v___x_4794_);
    lean_closure_set(v___f_4796_, 2, v___x_4795_);
    v___x_4797_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
        v_mvarId_4787_,
        v___f_4796_,
        v_a_4789_,
        v_a_4790_,
        v_a_4791_,
        v_a_4792_,
    );
    return v___x_4797_;
}
pub unsafe fn l_Lean_MVarId_admit___boxed(
    mut v_mvarId_4798_: *mut LeanObject,
    mut v_synthetic_4799_: *mut LeanObject,
    mut v_a_4800_: *mut LeanObject,
    mut v_a_4801_: *mut LeanObject,
    mut v_a_4802_: *mut LeanObject,
    mut v_a_4803_: *mut LeanObject,
    mut v_a_4804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_synthetic_boxed_4805_: u8 = 0;
    let mut v_res_4806_: *mut LeanObject = core::ptr::null_mut();
    v_synthetic_boxed_4805_ = (lean_unbox(v_synthetic_4799_) as u8);
    v_res_4806_ = l_Lean_MVarId_admit(
        v_mvarId_4798_,
        v_synthetic_boxed_4805_,
        v_a_4800_,
        v_a_4801_,
        v_a_4802_,
        v_a_4803_,
    );
    lean_dec(v_a_4803_);
    lean_dec_ref(v_a_4802_);
    lean_dec(v_a_4801_);
    lean_dec_ref(v_a_4800_);
    return v_res_4806_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(
    mut v_mvarId_4807_: *mut LeanObject,
    mut v_val_4808_: *mut LeanObject,
    mut v___y_4809_: *mut LeanObject,
    mut v___y_4810_: *mut LeanObject,
    mut v___y_4811_: *mut LeanObject,
    mut v___y_4812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4814_: *mut LeanObject = core::ptr::null_mut();
    v___x_4814_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___redArg(
        v_mvarId_4807_,
        v_val_4808_,
        v___y_4810_,
    );
    return v___x_4814_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0___boxed(
    mut v_mvarId_4815_: *mut LeanObject,
    mut v_val_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
    mut v___y_4821_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4822_: *mut LeanObject = core::ptr::null_mut();
    v_res_4822_ = l_Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0(
        v_mvarId_4815_,
        v_val_4816_,
        v___y_4817_,
        v___y_4818_,
        v___y_4819_,
        v___y_4820_,
    );
    lean_dec(v___y_4820_);
    lean_dec_ref(v___y_4819_);
    lean_dec(v___y_4818_);
    lean_dec_ref(v___y_4817_);
    return v_res_4822_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0(
    mut v_00_u03b2_4823_: *mut LeanObject,
    mut v_x_4824_: *mut LeanObject,
    mut v_x_4825_: *mut LeanObject,
    mut v_x_4826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4827_: *mut LeanObject = core::ptr::null_mut();
    v___x_4827_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0___redArg(v_x_4824_, v_x_4825_, v_x_4826_);
    return v___x_4827_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(
    mut v_00_u03b2_4828_: *mut LeanObject,
    mut v_x_4829_: *mut LeanObject,
    mut v_x_4830_: usize,
    mut v_x_4831_: usize,
    mut v_x_4832_: *mut LeanObject,
    mut v_x_4833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4834_: *mut LeanObject = core::ptr::null_mut();
    v___x_4834_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___redArg(v_x_4829_, v_x_4830_, v_x_4831_, v_x_4832_, v_x_4833_);
    return v___x_4834_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_4835_: *mut LeanObject,
    mut v_x_4836_: *mut LeanObject,
    mut v_x_4837_: *mut LeanObject,
    mut v_x_4838_: *mut LeanObject,
    mut v_x_4839_: *mut LeanObject,
    mut v_x_4840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1340__boxed_4841_: usize = 0;
    let mut v_x_1341__boxed_4842_: usize = 0;
    let mut v_res_4843_: *mut LeanObject = core::ptr::null_mut();
    v_x_1340__boxed_4841_ = lean_unbox_usize(v_x_4837_);
    lean_dec(v_x_4837_);
    v_x_1341__boxed_4842_ = lean_unbox_usize(v_x_4838_);
    lean_dec(v_x_4838_);
    v_res_4843_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2(v_00_u03b2_4835_, v_x_4836_, v_x_1340__boxed_4841_, v_x_1341__boxed_4842_, v_x_4839_, v_x_4840_);
    return v_res_4843_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_4844_: *mut LeanObject,
    mut v_n_4845_: *mut LeanObject,
    mut v_k_4846_: *mut LeanObject,
    mut v_v_4847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    v___x_4848_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3___redArg(v_n_4845_, v_k_4846_, v_v_4847_);
    return v___x_4848_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_4849_: *mut LeanObject,
    mut v_depth_4850_: usize,
    mut v_keys_4851_: *mut LeanObject,
    mut v_vals_4852_: *mut LeanObject,
    mut v_heq_4853_: *mut LeanObject,
    mut v_i_4854_: *mut LeanObject,
    mut v_entries_4855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4856_: *mut LeanObject = core::ptr::null_mut();
    v___x_4856_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_4850_, v_keys_4851_, v_vals_4852_, v_i_4854_, v_entries_4855_);
    return v___x_4856_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_4857_: *mut LeanObject,
    mut v_depth_4858_: *mut LeanObject,
    mut v_keys_4859_: *mut LeanObject,
    mut v_vals_4860_: *mut LeanObject,
    mut v_heq_4861_: *mut LeanObject,
    mut v_i_4862_: *mut LeanObject,
    mut v_entries_4863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4864_: usize = 0;
    let mut v_res_4865_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4864_ = lean_unbox_usize(v_depth_4858_);
    lean_dec(v_depth_4858_);
    v_res_4865_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_4857_, v_depth_boxed_4864_, v_keys_4859_, v_vals_4860_, v_heq_4861_, v_i_4862_, v_entries_4863_);
    lean_dec_ref(v_vals_4860_);
    lean_dec_ref(v_keys_4859_);
    return v_res_4865_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_4866_: *mut LeanObject,
    mut v_x_4867_: *mut LeanObject,
    mut v_x_4868_: *mut LeanObject,
    mut v_x_4869_: *mut LeanObject,
    mut v_x_4870_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4871_: *mut LeanObject = core::ptr::null_mut();
    v___x_4871_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_admit_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_4867_, v_x_4868_, v_x_4869_, v_x_4870_);
    return v___x_4871_;
}
pub unsafe fn l_Lean_MVarId_headBetaType(
    mut v_mvarId_4872_: *mut LeanObject,
    mut v_a_4873_: *mut LeanObject,
    mut v_a_4874_: *mut LeanObject,
    mut v_a_4875_: *mut LeanObject,
    mut v_a_4876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4885_: u8 = 0;
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_mvarId_4872_);
                v___x_4878_ = l_Lean_MVarId_getType(
                    v_mvarId_4872_,
                    v_a_4873_,
                    v_a_4874_,
                    v_a_4875_,
                    v_a_4876_,
                );
                if lean_obj_tag(v___x_4878_) == 0 {
                    v_a_4879_ = lean_ctor_get(v___x_4878_, 0);
                    lean_inc(v_a_4879_);
                    lean_dec_ref_known(v___x_4878_, 1);
                    v___x_4880_ = l_Lean_Expr_headBeta(v_a_4879_);
                    v___x_4881_ =
                        l_Lean_MVarId_setType___redArg(v_mvarId_4872_, v___x_4880_, v_a_4874_);
                    return v___x_4881_;
                } else {
                    lean_dec(v_mvarId_4872_);
                    v_a_4882_ = lean_ctor_get(v___x_4878_, 0);
                    v_isSharedCheck_4889_ = (!lean_is_exclusive(v___x_4878_)) as u8;
                    if v_isSharedCheck_4889_ == 0 {
                        v___x_4884_ = v___x_4878_;
                        v_isShared_4885_ = v_isSharedCheck_4889_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4882_);
                        lean_dec(v___x_4878_);
                        v___x_4884_ = lean_box(0);
                        v_isShared_4885_ = v_isSharedCheck_4889_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4885_ == 0 {
                    v___x_4887_ = v___x_4884_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
                    v___x_4887_ = v_reuseFailAlloc_4888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_headBetaType___boxed(
    mut v_mvarId_4890_: *mut LeanObject,
    mut v_a_4891_: *mut LeanObject,
    mut v_a_4892_: *mut LeanObject,
    mut v_a_4893_: *mut LeanObject,
    mut v_a_4894_: *mut LeanObject,
    mut v_a_4895_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4896_: *mut LeanObject = core::ptr::null_mut();
    v_res_4896_ =
        l_Lean_MVarId_headBetaType(v_mvarId_4890_, v_a_4891_, v_a_4892_, v_a_4893_, v_a_4894_);
    lean_dec(v_a_4894_);
    lean_dec_ref(v_a_4893_);
    lean_dec(v_a_4892_);
    lean_dec_ref(v_a_4891_);
    return v_res_4896_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(
    mut v_a_4897_: *mut LeanObject,
    mut v_x_4898_: *mut LeanObject,
) -> u8 {
    let mut v___x_4899_: u8 = 0;
    let mut v_key_4900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4898_) == 0 {
                    v___x_4899_ = 0;
                    return v___x_4899_;
                } else {
                    v_key_4900_ = lean_ctor_get(v_x_4898_, 0);
                    v_tail_4901_ = lean_ctor_get(v_x_4898_, 2);
                    v___x_4902_ = l_Lean_instBEqFVarId_beq(v_key_4900_, v_a_4897_);
                    if v___x_4902_ == 0 {
                        v_x_4898_ = v_tail_4901_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4902_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg___boxed(
    mut v_a_4904_: *mut LeanObject,
    mut v_x_4905_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4906_: u8 = 0;
    let mut v_r_4907_: *mut LeanObject = core::ptr::null_mut();
    v_res_4906_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_4904_, v_x_4905_);
    lean_dec(v_x_4905_);
    lean_dec(v_a_4904_);
    v_r_4907_ = lean_box((v_res_4906_) as usize);
    return v_r_4907_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(
    mut v_a_4908_: *mut LeanObject,
    mut v_x_4909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4915_: u8 = 0;
    let mut v___x_4916_: u8 = 0;
    let mut v___x_4917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4909_) == 0 {
                    return v_x_4909_;
                } else {
                    v_key_4910_ = lean_ctor_get(v_x_4909_, 0);
                    v_value_4911_ = lean_ctor_get(v_x_4909_, 1);
                    v_tail_4912_ = lean_ctor_get(v_x_4909_, 2);
                    v_isSharedCheck_4921_ = (!lean_is_exclusive(v_x_4909_)) as u8;
                    if v_isSharedCheck_4921_ == 0 {
                        v___x_4914_ = v_x_4909_;
                        v_isShared_4915_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4912_);
                        lean_inc(v_value_4911_);
                        lean_inc(v_key_4910_);
                        lean_dec(v_x_4909_);
                        v___x_4914_ = lean_box(0);
                        v_isShared_4915_ = v_isSharedCheck_4921_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4916_ = l_Lean_instBEqFVarId_beq(v_key_4910_, v_a_4908_);
                if v___x_4916_ == 0 {
                    v___x_4917_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_4908_, v_tail_4912_);
                    if v_isShared_4915_ == 0 {
                        lean_ctor_set(v___x_4914_, 2, v___x_4917_);
                        v___x_4919_ = v___x_4914_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_key_4910_);
                        lean_ctor_set(v_reuseFailAlloc_4920_, 1, v_value_4911_);
                        lean_ctor_set(v_reuseFailAlloc_4920_, 2, v___x_4917_);
                        v___x_4919_ = v_reuseFailAlloc_4920_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4914_);
                    lean_dec(v_value_4911_);
                    lean_dec(v_key_4910_);
                    return v_tail_4912_;
                }
            }
            2 => {
                return v___x_4919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg___boxed(
    mut v_a_4922_: *mut LeanObject,
    mut v_x_4923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4924_: *mut LeanObject = core::ptr::null_mut();
    v_res_4924_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_4922_, v_x_4923_);
    lean_dec(v_a_4922_);
    return v_res_4924_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(
    mut v_m_4925_: *mut LeanObject,
    mut v_a_4926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_4927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4930_: u64 = 0;
    let mut v___x_4931_: u64 = 0;
    let mut v___x_4932_: u64 = 0;
    let mut v_fold_4933_: u64 = 0;
    let mut v___x_4934_: u64 = 0;
    let mut v___x_4935_: u64 = 0;
    let mut v___x_4936_: u64 = 0;
    let mut v___x_4937_: usize = 0;
    let mut v___x_4938_: usize = 0;
    let mut v___x_4939_: usize = 0;
    let mut v___x_4940_: usize = 0;
    let mut v___x_4941_: usize = 0;
    let mut v_bkt_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: u8 = 0;
    let mut v___x_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v___x_4947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4956_: u8 = 0;
    let mut v_unused_4957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_4927_ = lean_ctor_get(v_m_4925_, 0);
                v_buckets_4928_ = lean_ctor_get(v_m_4925_, 1);
                v___x_4929_ = lean_array_get_size(v_buckets_4928_);
                v___x_4930_ = l_Lean_instHashableFVarId_hash(v_a_4926_);
                v___x_4931_ = 32u64;
                v___x_4932_ = lean_uint64_shift_right(v___x_4930_, v___x_4931_);
                v_fold_4933_ = lean_uint64_xor(v___x_4930_, v___x_4932_);
                v___x_4934_ = 16u64;
                v___x_4935_ = lean_uint64_shift_right(v_fold_4933_, v___x_4934_);
                v___x_4936_ = lean_uint64_xor(v_fold_4933_, v___x_4935_);
                v___x_4937_ = lean_uint64_to_usize(v___x_4936_);
                v___x_4938_ = lean_usize_of_nat(v___x_4929_);
                v___x_4939_ = 1usize;
                v___x_4940_ = lean_usize_sub(v___x_4938_, v___x_4939_);
                v___x_4941_ = lean_usize_land(v___x_4937_, v___x_4940_);
                v_bkt_4942_ = lean_array_uget_borrowed(v_buckets_4928_, v___x_4941_);
                v___x_4943_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_4926_, v_bkt_4942_);
                if v___x_4943_ == 0 {
                    return v_m_4925_;
                } else {
                    lean_inc(v_bkt_4942_);
                    lean_inc_ref(v_buckets_4928_);
                    lean_inc(v_size_4927_);
                    v_isSharedCheck_4956_ = (!lean_is_exclusive(v_m_4925_)) as u8;
                    if v_isSharedCheck_4956_ == 0 {
                        v_unused_4957_ = lean_ctor_get(v_m_4925_, 1);
                        lean_dec(v_unused_4957_);
                        v_unused_4958_ = lean_ctor_get(v_m_4925_, 0);
                        lean_dec(v_unused_4958_);
                        v___x_4945_ = v_m_4925_;
                        v_isShared_4946_ = v_isSharedCheck_4956_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_4925_);
                        v___x_4945_ = lean_box(0);
                        v_isShared_4946_ = v_isSharedCheck_4956_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4947_ = lean_box(0);
                v_buckets_x27_4948_ = lean_array_uset(v_buckets_4928_, v___x_4941_, v___x_4947_);
                v___x_4949_ = lean_unsigned_to_nat(1);
                v___x_4950_ = lean_nat_sub(v_size_4927_, v___x_4949_);
                lean_dec(v_size_4927_);
                v___x_4951_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_4926_, v_bkt_4942_);
                v___x_4952_ = lean_array_uset(v_buckets_x27_4948_, v___x_4941_, v___x_4951_);
                if v_isShared_4946_ == 0 {
                    lean_ctor_set(v___x_4945_, 1, v___x_4952_);
                    lean_ctor_set(v___x_4945_, 0, v___x_4950_);
                    v___x_4954_ = v___x_4945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4950_);
                    lean_ctor_set(v_reuseFailAlloc_4955_, 1, v___x_4952_);
                    v___x_4954_ = v_reuseFailAlloc_4955_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg___boxed(
    mut v_m_4959_: *mut LeanObject,
    mut v_a_4960_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4961_: *mut LeanObject = core::ptr::null_mut();
    v_res_4961_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_4959_, v_a_4960_);
    lean_dec(v_a_4960_);
    return v_res_4961_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__0(
    mut v_e_4962_: *mut LeanObject,
    mut v___y_4963_: *mut LeanObject,
    mut v___y_4964_: *mut LeanObject,
    mut v___y_4965_: *mut LeanObject,
    mut v___y_4966_: *mut LeanObject,
    mut v___y_4967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: *mut LeanObject = core::ptr::null_mut();
    v___x_4969_ = lean_st_ref_take(v___y_4963_);
    v___x_4970_ = l_Lean_Expr_fvarId_x21(v_e_4962_);
    v___x_4971_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_4969_, v___x_4970_);
    lean_dec(v___x_4970_);
    v___x_4972_ = lean_st_ref_set(v___y_4963_, v___x_4971_);
    v___x_4973_ = lean_box(0);
    v___x_4974_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4974_, 0, v___x_4973_);
    return v___x_4974_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__0___boxed(
    mut v_e_4975_: *mut LeanObject,
    mut v___y_4976_: *mut LeanObject,
    mut v___y_4977_: *mut LeanObject,
    mut v___y_4978_: *mut LeanObject,
    mut v___y_4979_: *mut LeanObject,
    mut v___y_4980_: *mut LeanObject,
    mut v___y_4981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4982_: *mut LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Lean_MVarId_getNondepPropHyps___lam__0(
        v_e_4975_,
        v___y_4976_,
        v___y_4977_,
        v___y_4978_,
        v___y_4979_,
        v___y_4980_,
    );
    lean_dec(v___y_4980_);
    lean_dec_ref(v___y_4979_);
    lean_dec(v___y_4978_);
    lean_dec_ref(v___y_4977_);
    lean_dec(v___y_4976_);
    lean_dec_ref(v_e_4975_);
    return v_res_4982_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__1(
    mut v_____r_4983_: *mut LeanObject,
    mut v___y_4984_: *mut LeanObject,
    mut v___y_4985_: *mut LeanObject,
    mut v___y_4986_: *mut LeanObject,
    mut v___y_4987_: *mut LeanObject,
    mut v___y_4988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4991_: *mut LeanObject = core::ptr::null_mut();
    v___x_4990_ = lean_st_ref_get(v___y_4984_);
    v___x_4991_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4991_, 0, v___x_4990_);
    return v___x_4991_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__1___boxed(
    mut v_____r_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
    mut v___y_4995_: *mut LeanObject,
    mut v___y_4996_: *mut LeanObject,
    mut v___y_4997_: *mut LeanObject,
    mut v___y_4998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4999_: *mut LeanObject = core::ptr::null_mut();
    v_res_4999_ = l_Lean_MVarId_getNondepPropHyps___lam__1(
        v_____r_4992_,
        v___y_4993_,
        v___y_4994_,
        v___y_4995_,
        v___y_4996_,
        v___y_4997_,
    );
    lean_dec(v___y_4997_);
    lean_dec_ref(v___y_4996_);
    lean_dec(v___y_4995_);
    lean_dec_ref(v___y_4994_);
    lean_dec(v___y_4993_);
    return v_res_4999_;
}
pub unsafe fn _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0()
-> usize {
    let mut v___x_5000_: usize = 0;
    let mut v___x_5001_: usize = 0;
    let mut v___x_5002_: usize = 0;
    v___x_5000_ = 1usize;
    v___x_5001_ = 8192usize;
    v___x_5002_ = lean_usize_sub(v___x_5001_, v___x_5000_);
    return v___x_5002_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(
    mut v_e_5003_: *mut LeanObject,
    mut v_a_5004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_5007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5008_: usize = 0;
    let mut v___x_5009_: usize = 0;
    let mut v___x_5010_: usize = 0;
    let mut v___x_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: usize = 0;
    let mut v___x_5013_: u8 = 0;
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_5015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_5016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5019_: u8 = 0;
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5027_: u8 = 0;
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5006_ = lean_st_ref_get(v_a_5004_);
                v_visited_5007_ = lean_ctor_get(v___x_5006_, 0);
                lean_inc_ref(v_visited_5007_);
                lean_dec(v___x_5006_);
                v___x_5008_ = lean_ptr_addr(v_e_5003_);
                v___x_5009_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0_once), _init_l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___closed__0);
                v___x_5010_ = lean_usize_mod(v___x_5008_, v___x_5009_);
                v___x_5011_ = lean_array_uget(v_visited_5007_, v___x_5010_);
                lean_dec_ref(v_visited_5007_);
                v___x_5012_ = lean_ptr_addr(v___x_5011_);
                lean_dec(v___x_5011_);
                v___x_5013_ = lean_usize_dec_eq(v___x_5012_, v___x_5008_);
                if v___x_5013_ == 0 {
                    v___x_5014_ = lean_st_ref_take(v_a_5004_);
                    v_visited_5015_ = lean_ctor_get(v___x_5014_, 0);
                    v_checked_5016_ = lean_ctor_get(v___x_5014_, 1);
                    v_isSharedCheck_5027_ = (!lean_is_exclusive(v___x_5014_)) as u8;
                    if v_isSharedCheck_5027_ == 0 {
                        v___x_5018_ = v___x_5014_;
                        v_isShared_5019_ = v_isSharedCheck_5027_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_checked_5016_);
                        lean_inc(v_visited_5015_);
                        lean_dec(v___x_5014_);
                        v___x_5018_ = lean_box(0);
                        v_isShared_5019_ = v_isSharedCheck_5027_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_5003_);
                    v___x_5028_ = lean_box((v___x_5013_) as usize);
                    v___x_5029_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5029_, 0, v___x_5028_);
                    return v___x_5029_;
                }
            }
            1 => {
                v___x_5020_ = lean_array_uset(v_visited_5015_, v___x_5010_, v_e_5003_);
                if v_isShared_5019_ == 0 {
                    lean_ctor_set(v___x_5018_, 0, v___x_5020_);
                    v___x_5022_ = v___x_5018_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5026_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5020_);
                    lean_ctor_set(v_reuseFailAlloc_5026_, 1, v_checked_5016_);
                    v___x_5022_ = v_reuseFailAlloc_5026_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5023_ = lean_st_ref_set(v_a_5004_, v___x_5022_);
                v___x_5024_ = lean_box((v___x_5013_) as usize);
                v___x_5025_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5025_, 0, v___x_5024_);
                return v___x_5025_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg___boxed(
    mut v_e_5030_: *mut LeanObject,
    mut v_a_5031_: *mut LeanObject,
    mut v___y_5032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5033_: *mut LeanObject = core::ptr::null_mut();
    v_res_5033_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_5030_, v_a_5031_);
    lean_dec(v_a_5031_);
    return v_res_5033_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(
    mut v_a_5034_: *mut LeanObject,
    mut v_x_5035_: *mut LeanObject,
) -> u8 {
    let mut v___x_5036_: u8 = 0;
    let mut v_key_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5035_) == 0 {
                    v___x_5036_ = 0;
                    return v___x_5036_;
                } else {
                    v_key_5037_ = lean_ctor_get(v_x_5035_, 0);
                    v_tail_5038_ = lean_ctor_get(v_x_5035_, 2);
                    v___x_5039_ = lean_expr_eqv(v_key_5037_, v_a_5034_);
                    if v___x_5039_ == 0 {
                        v_x_5035_ = v_tail_5038_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5039_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg___boxed(
    mut v_a_5041_: *mut LeanObject,
    mut v_x_5042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5043_: u8 = 0;
    let mut v_r_5044_: *mut LeanObject = core::ptr::null_mut();
    v_res_5043_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_5041_, v_x_5042_);
    lean_dec(v_x_5042_);
    lean_dec_ref(v_a_5041_);
    v_r_5044_ = lean_box((v_res_5043_) as usize);
    return v_r_5044_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(
    mut v_x_5045_: *mut LeanObject,
    mut v_x_5046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5052_: u8 = 0;
    let mut v___x_5053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: u64 = 0;
    let mut v___x_5055_: u64 = 0;
    let mut v___x_5056_: u64 = 0;
    let mut v_fold_5057_: u64 = 0;
    let mut v___x_5058_: u64 = 0;
    let mut v___x_5059_: u64 = 0;
    let mut v___x_5060_: u64 = 0;
    let mut v___x_5061_: usize = 0;
    let mut v___x_5062_: usize = 0;
    let mut v___x_5063_: usize = 0;
    let mut v___x_5064_: usize = 0;
    let mut v___x_5065_: usize = 0;
    let mut v___x_5066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5072_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5046_) == 0 {
                    return v_x_5045_;
                } else {
                    v_key_5047_ = lean_ctor_get(v_x_5046_, 0);
                    v_value_5048_ = lean_ctor_get(v_x_5046_, 1);
                    v_tail_5049_ = lean_ctor_get(v_x_5046_, 2);
                    v_isSharedCheck_5072_ = (!lean_is_exclusive(v_x_5046_)) as u8;
                    if v_isSharedCheck_5072_ == 0 {
                        v___x_5051_ = v_x_5046_;
                        v_isShared_5052_ = v_isSharedCheck_5072_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5049_);
                        lean_inc(v_value_5048_);
                        lean_inc(v_key_5047_);
                        lean_dec(v_x_5046_);
                        v___x_5051_ = lean_box(0);
                        v_isShared_5052_ = v_isSharedCheck_5072_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5053_ = lean_array_get_size(v_x_5045_);
                v___x_5054_ = l_Lean_Expr_hash(v_key_5047_);
                v___x_5055_ = 32u64;
                v___x_5056_ = lean_uint64_shift_right(v___x_5054_, v___x_5055_);
                v_fold_5057_ = lean_uint64_xor(v___x_5054_, v___x_5056_);
                v___x_5058_ = 16u64;
                v___x_5059_ = lean_uint64_shift_right(v_fold_5057_, v___x_5058_);
                v___x_5060_ = lean_uint64_xor(v_fold_5057_, v___x_5059_);
                v___x_5061_ = lean_uint64_to_usize(v___x_5060_);
                v___x_5062_ = lean_usize_of_nat(v___x_5053_);
                v___x_5063_ = 1usize;
                v___x_5064_ = lean_usize_sub(v___x_5062_, v___x_5063_);
                v___x_5065_ = lean_usize_land(v___x_5061_, v___x_5064_);
                v___x_5066_ = lean_array_uget_borrowed(v_x_5045_, v___x_5065_);
                lean_inc(v___x_5066_);
                if v_isShared_5052_ == 0 {
                    lean_ctor_set(v___x_5051_, 2, v___x_5066_);
                    v___x_5068_ = v___x_5051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5071_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5071_, 0, v_key_5047_);
                    lean_ctor_set(v_reuseFailAlloc_5071_, 1, v_value_5048_);
                    lean_ctor_set(v_reuseFailAlloc_5071_, 2, v___x_5066_);
                    v___x_5068_ = v_reuseFailAlloc_5071_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5069_ = lean_array_uset(v_x_5045_, v___x_5065_, v___x_5068_);
                v_x_5045_ = v___x_5069_;
                v_x_5046_ = v_tail_5049_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(
    mut v_i_5073_: *mut LeanObject,
    mut v_source_5074_: *mut LeanObject,
    mut v_target_5075_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5077_: u8 = 0;
    let mut v_es_5078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_5080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5083_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5076_ = lean_array_get_size(v_source_5074_);
                v___x_5077_ = lean_nat_dec_lt(v_i_5073_, v___x_5076_);
                if v___x_5077_ == 0 {
                    lean_dec_ref(v_source_5074_);
                    lean_dec(v_i_5073_);
                    return v_target_5075_;
                } else {
                    v_es_5078_ = lean_array_fget(v_source_5074_, v_i_5073_);
                    v___x_5079_ = lean_box(0);
                    v_source_5080_ = lean_array_fset(v_source_5074_, v_i_5073_, v___x_5079_);
                    v_target_5081_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_target_5075_, v_es_5078_);
                    v___x_5082_ = lean_unsigned_to_nat(1);
                    v___x_5083_ = lean_nat_add(v_i_5073_, v___x_5082_);
                    lean_dec(v_i_5073_);
                    v_i_5073_ = v___x_5083_;
                    v_source_5074_ = v_source_5080_;
                    v_target_5075_ = v_target_5081_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(
    mut v_data_5085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    v___x_5086_ = lean_array_get_size(v_data_5085_);
    v___x_5087_ = lean_unsigned_to_nat(2);
    v_nbuckets_5088_ = lean_nat_mul(v___x_5086_, v___x_5087_);
    v___x_5089_ = lean_unsigned_to_nat(0);
    v___x_5090_ = lean_box(0);
    v___x_5091_ = lean_mk_array(v_nbuckets_5088_, v___x_5090_);
    v___x_5092_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v___x_5089_, v_data_5085_, v___x_5091_);
    return v___x_5092_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(
    mut v_m_5093_: *mut LeanObject,
    mut v_a_5094_: *mut LeanObject,
    mut v_b_5095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5099_: u64 = 0;
    let mut v___x_5100_: u64 = 0;
    let mut v___x_5101_: u64 = 0;
    let mut v_fold_5102_: u64 = 0;
    let mut v___x_5103_: u64 = 0;
    let mut v___x_5104_: u64 = 0;
    let mut v___x_5105_: u64 = 0;
    let mut v___x_5106_: usize = 0;
    let mut v___x_5107_: usize = 0;
    let mut v___x_5108_: usize = 0;
    let mut v___x_5109_: usize = 0;
    let mut v___x_5110_: usize = 0;
    let mut v_bkt_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: u8 = 0;
    let mut v___x_5114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5115_: u8 = 0;
    let mut v___x_5116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5125_: u8 = 0;
    let mut v_val_5126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut v_unused_5134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5096_ = lean_ctor_get(v_m_5093_, 0);
                v_buckets_5097_ = lean_ctor_get(v_m_5093_, 1);
                v___x_5098_ = lean_array_get_size(v_buckets_5097_);
                v___x_5099_ = l_Lean_Expr_hash(v_a_5094_);
                v___x_5100_ = 32u64;
                v___x_5101_ = lean_uint64_shift_right(v___x_5099_, v___x_5100_);
                v_fold_5102_ = lean_uint64_xor(v___x_5099_, v___x_5101_);
                v___x_5103_ = 16u64;
                v___x_5104_ = lean_uint64_shift_right(v_fold_5102_, v___x_5103_);
                v___x_5105_ = lean_uint64_xor(v_fold_5102_, v___x_5104_);
                v___x_5106_ = lean_uint64_to_usize(v___x_5105_);
                v___x_5107_ = lean_usize_of_nat(v___x_5098_);
                v___x_5108_ = 1usize;
                v___x_5109_ = lean_usize_sub(v___x_5107_, v___x_5108_);
                v___x_5110_ = lean_usize_land(v___x_5106_, v___x_5109_);
                v_bkt_5111_ = lean_array_uget_borrowed(v_buckets_5097_, v___x_5110_);
                v___x_5112_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_5094_, v_bkt_5111_);
                if v___x_5112_ == 0 {
                    lean_inc_ref(v_buckets_5097_);
                    lean_inc(v_size_5096_);
                    v_isSharedCheck_5133_ = (!lean_is_exclusive(v_m_5093_)) as u8;
                    if v_isSharedCheck_5133_ == 0 {
                        v_unused_5134_ = lean_ctor_get(v_m_5093_, 1);
                        lean_dec(v_unused_5134_);
                        v_unused_5135_ = lean_ctor_get(v_m_5093_, 0);
                        lean_dec(v_unused_5135_);
                        v___x_5114_ = v_m_5093_;
                        v_isShared_5115_ = v_isSharedCheck_5133_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_5093_);
                        v___x_5114_ = lean_box(0);
                        v_isShared_5115_ = v_isSharedCheck_5133_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_5095_);
                    lean_dec_ref(v_a_5094_);
                    return v_m_5093_;
                }
            }
            1 => {
                v___x_5116_ = lean_unsigned_to_nat(1);
                v_size_x27_5117_ = lean_nat_add(v_size_5096_, v___x_5116_);
                lean_dec(v_size_5096_);
                lean_inc(v_bkt_5111_);
                v___x_5118_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5118_, 0, v_a_5094_);
                lean_ctor_set(v___x_5118_, 1, v_b_5095_);
                lean_ctor_set(v___x_5118_, 2, v_bkt_5111_);
                v_buckets_x27_5119_ = lean_array_uset(v_buckets_5097_, v___x_5110_, v___x_5118_);
                v___x_5120_ = lean_unsigned_to_nat(4);
                v___x_5121_ = lean_nat_mul(v_size_x27_5117_, v___x_5120_);
                v___x_5122_ = lean_unsigned_to_nat(3);
                v___x_5123_ = lean_nat_div(v___x_5121_, v___x_5122_);
                lean_dec(v___x_5121_);
                v___x_5124_ = lean_array_get_size(v_buckets_x27_5119_);
                v___x_5125_ = lean_nat_dec_le(v___x_5123_, v___x_5124_);
                lean_dec(v___x_5123_);
                if v___x_5125_ == 0 {
                    v_val_5126_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_buckets_x27_5119_);
                    if v_isShared_5115_ == 0 {
                        lean_ctor_set(v___x_5114_, 1, v_val_5126_);
                        lean_ctor_set(v___x_5114_, 0, v_size_x27_5117_);
                        v___x_5128_ = v___x_5114_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5129_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5129_, 0, v_size_x27_5117_);
                        lean_ctor_set(v_reuseFailAlloc_5129_, 1, v_val_5126_);
                        v___x_5128_ = v_reuseFailAlloc_5129_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5115_ == 0 {
                        lean_ctor_set(v___x_5114_, 1, v_buckets_x27_5119_);
                        lean_ctor_set(v___x_5114_, 0, v_size_x27_5117_);
                        v___x_5131_ = v___x_5114_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_size_x27_5117_);
                        lean_ctor_set(v_reuseFailAlloc_5132_, 1, v_buckets_x27_5119_);
                        v___x_5131_ = v_reuseFailAlloc_5132_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5128_;
            }
            3 => {
                return v___x_5131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(
    mut v_m_5136_: *mut LeanObject,
    mut v_a_5137_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_5138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5140_: u64 = 0;
    let mut v___x_5141_: u64 = 0;
    let mut v___x_5142_: u64 = 0;
    let mut v_fold_5143_: u64 = 0;
    let mut v___x_5144_: u64 = 0;
    let mut v___x_5145_: u64 = 0;
    let mut v___x_5146_: u64 = 0;
    let mut v___x_5147_: usize = 0;
    let mut v___x_5148_: usize = 0;
    let mut v___x_5149_: usize = 0;
    let mut v___x_5150_: usize = 0;
    let mut v___x_5151_: usize = 0;
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5153_: u8 = 0;
    v_buckets_5138_ = lean_ctor_get(v_m_5136_, 1);
    v___x_5139_ = lean_array_get_size(v_buckets_5138_);
    v___x_5140_ = l_Lean_Expr_hash(v_a_5137_);
    v___x_5141_ = 32u64;
    v___x_5142_ = lean_uint64_shift_right(v___x_5140_, v___x_5141_);
    v_fold_5143_ = lean_uint64_xor(v___x_5140_, v___x_5142_);
    v___x_5144_ = 16u64;
    v___x_5145_ = lean_uint64_shift_right(v_fold_5143_, v___x_5144_);
    v___x_5146_ = lean_uint64_xor(v_fold_5143_, v___x_5145_);
    v___x_5147_ = lean_uint64_to_usize(v___x_5146_);
    v___x_5148_ = lean_usize_of_nat(v___x_5139_);
    v___x_5149_ = 1usize;
    v___x_5150_ = lean_usize_sub(v___x_5148_, v___x_5149_);
    v___x_5151_ = lean_usize_land(v___x_5147_, v___x_5150_);
    v___x_5152_ = lean_array_uget_borrowed(v_buckets_5138_, v___x_5151_);
    v___x_5153_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_5137_, v___x_5152_);
    return v___x_5153_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg___boxed(
    mut v_m_5154_: *mut LeanObject,
    mut v_a_5155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5156_: u8 = 0;
    let mut v_r_5157_: *mut LeanObject = core::ptr::null_mut();
    v_res_5156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_5154_, v_a_5155_);
    lean_dec_ref(v_a_5155_);
    lean_dec_ref(v_m_5154_);
    v_r_5157_ = lean_box((v_res_5156_) as usize);
    return v_r_5157_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(
    mut v_e_5158_: *mut LeanObject,
    mut v_a_5159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_5162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5163_: u8 = 0;
    let mut v___x_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_5165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_checked_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5169_: u8 = 0;
    let mut v___x_5170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5178_: u8 = 0;
    let mut v___x_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5161_ = lean_st_ref_get(v_a_5159_);
                v_checked_5162_ = lean_ctor_get(v___x_5161_, 1);
                lean_inc_ref(v_checked_5162_);
                lean_dec(v___x_5161_);
                v___x_5163_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_checked_5162_, v_e_5158_);
                lean_dec_ref(v_checked_5162_);
                if v___x_5163_ == 0 {
                    v___x_5164_ = lean_st_ref_take(v_a_5159_);
                    v_visited_5165_ = lean_ctor_get(v___x_5164_, 0);
                    v_checked_5166_ = lean_ctor_get(v___x_5164_, 1);
                    v_isSharedCheck_5178_ = (!lean_is_exclusive(v___x_5164_)) as u8;
                    if v_isSharedCheck_5178_ == 0 {
                        v___x_5168_ = v___x_5164_;
                        v_isShared_5169_ = v_isSharedCheck_5178_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_checked_5166_);
                        lean_inc(v_visited_5165_);
                        lean_dec(v___x_5164_);
                        v___x_5168_ = lean_box(0);
                        v_isShared_5169_ = v_isSharedCheck_5178_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_5158_);
                    v___x_5179_ = lean_box((v___x_5163_) as usize);
                    v___x_5180_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5180_, 0, v___x_5179_);
                    return v___x_5180_;
                }
            }
            1 => {
                v___x_5170_ = lean_box(0);
                v___x_5171_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_checked_5166_, v_e_5158_, v___x_5170_);
                if v_isShared_5169_ == 0 {
                    lean_ctor_set(v___x_5168_, 1, v___x_5171_);
                    v___x_5173_ = v___x_5168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5177_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5177_, 0, v_visited_5165_);
                    lean_ctor_set(v_reuseFailAlloc_5177_, 1, v___x_5171_);
                    v___x_5173_ = v_reuseFailAlloc_5177_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5174_ = lean_st_ref_set(v_a_5159_, v___x_5173_);
                v___x_5175_ = lean_box((v___x_5163_) as usize);
                v___x_5176_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5176_, 0, v___x_5175_);
                return v___x_5176_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg___boxed(
    mut v_e_5181_: *mut LeanObject,
    mut v_a_5182_: *mut LeanObject,
    mut v___y_5183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5184_: *mut LeanObject = core::ptr::null_mut();
    v_res_5184_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_5181_, v_a_5182_);
    lean_dec(v_a_5182_);
    return v_res_5184_;
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(
    mut v_p_5185_: *mut LeanObject,
    mut v_f_5186_: *mut LeanObject,
    mut v_stopWhenVisited_5187_: u8,
    mut v_e_5188_: *mut LeanObject,
    mut v_a_5189_: *mut LeanObject,
    mut v___y_5190_: *mut LeanObject,
    mut v___y_5191_: *mut LeanObject,
    mut v___y_5192_: *mut LeanObject,
    mut v___y_5193_: *mut LeanObject,
    mut v___y_5194_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_5202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_b_5203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_5214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderType_5216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fn_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_5225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_5228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_5230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5238_: u8 = 0;
    let mut v___x_5239_: u8 = 0;
    let mut v___x_5240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: u8 = 0;
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: u8 = 0;
    let mut v___x_5245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5248_: u8 = 0;
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5253_: u8 = 0;
    let mut v_unused_5254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5258_: u8 = 0;
    let mut v___x_5260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5262_: u8 = 0;
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_a_5268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_5188_);
                v___x_5234_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_5188_, v_a_5189_);
                if lean_obj_tag(v___x_5234_) == 0 {
                    v_a_5235_ = lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5267_ = (!lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5267_ == 0 {
                        v___x_5237_ = v___x_5234_;
                        v_isShared_5238_ = v_isSharedCheck_5267_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5235_);
                        lean_dec(v___x_5234_);
                        v___x_5237_ = lean_box(0);
                        v_isShared_5238_ = v_isSharedCheck_5267_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_5188_);
                    lean_dec_ref(v_f_5186_);
                    lean_dec_ref(v_p_5185_);
                    v_a_5268_ = lean_ctor_get(v___x_5234_, 0);
                    v_isSharedCheck_5275_ = (!lean_is_exclusive(v___x_5234_)) as u8;
                    if v_isSharedCheck_5275_ == 0 {
                        v___x_5270_ = v___x_5234_;
                        v_isShared_5271_ = v_isSharedCheck_5275_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_5268_);
                        lean_dec(v___x_5234_);
                        v___x_5270_ = lean_box(0);
                        v_isShared_5271_ = v_isSharedCheck_5275_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_f_5186_);
                lean_inc_ref(v_p_5185_);
                v___x_5205_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_d_5202_, v___y_5204_, v___y_5200_, v___y_5198_, v___y_5199_, v___y_5197_, v___y_5201_);
                if lean_obj_tag(v___x_5205_) == 0 {
                    lean_dec_ref_known(v___x_5205_, 1);
                    v_e_5188_ = v_b_5203_;
                    v_a_5189_ = v___y_5204_;
                    v___y_5190_ = v___y_5200_;
                    v___y_5191_ = v___y_5198_;
                    v___y_5192_ = v___y_5199_;
                    v___y_5193_ = v___y_5197_;
                    v___y_5194_ = v___y_5201_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_b_5203_);
                    lean_dec_ref(v_f_5186_);
                    lean_dec_ref(v_p_5185_);
                    return v___x_5205_;
                }
            }
            2 => match lean_obj_tag(v_e_5188_) {
                7 => {
                    v_binderType_5214_ = lean_ctor_get(v_e_5188_, 1);
                    lean_inc_ref(v_binderType_5214_);
                    v_body_5215_ = lean_ctor_get(v_e_5188_, 2);
                    lean_inc_ref(v_body_5215_);
                    lean_dec_ref_known(v_e_5188_, 3);
                    v___y_5197_ = v___y_5212_;
                    v___y_5198_ = v___y_5210_;
                    v___y_5199_ = v___y_5211_;
                    v___y_5200_ = v___y_5209_;
                    v___y_5201_ = v___y_5213_;
                    v_d_5202_ = v_binderType_5214_;
                    v_b_5203_ = v_body_5215_;
                    v___y_5204_ = v___y_5208_;
                    state = 1;
                    continue;
                }
                6 => {
                    v_binderType_5216_ = lean_ctor_get(v_e_5188_, 1);
                    lean_inc_ref(v_binderType_5216_);
                    v_body_5217_ = lean_ctor_get(v_e_5188_, 2);
                    lean_inc_ref(v_body_5217_);
                    lean_dec_ref_known(v_e_5188_, 3);
                    v___y_5197_ = v___y_5212_;
                    v___y_5198_ = v___y_5210_;
                    v___y_5199_ = v___y_5211_;
                    v___y_5200_ = v___y_5209_;
                    v___y_5201_ = v___y_5213_;
                    v_d_5202_ = v_binderType_5216_;
                    v_b_5203_ = v_body_5217_;
                    v___y_5204_ = v___y_5208_;
                    state = 1;
                    continue;
                }
                8 => {
                    v_type_5218_ = lean_ctor_get(v_e_5188_, 1);
                    lean_inc_ref(v_type_5218_);
                    v_value_5219_ = lean_ctor_get(v_e_5188_, 2);
                    lean_inc_ref(v_value_5219_);
                    v_body_5220_ = lean_ctor_get(v_e_5188_, 3);
                    lean_inc_ref(v_body_5220_);
                    lean_dec_ref_known(v_e_5188_, 4);
                    lean_inc_ref(v_f_5186_);
                    lean_inc_ref(v_p_5185_);
                    v___x_5221_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_type_5218_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
                    if lean_obj_tag(v___x_5221_) == 0 {
                        lean_dec_ref_known(v___x_5221_, 1);
                        lean_inc_ref(v_f_5186_);
                        lean_inc_ref(v_p_5185_);
                        v___x_5222_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_value_5219_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
                        if lean_obj_tag(v___x_5222_) == 0 {
                            lean_dec_ref_known(v___x_5222_, 1);
                            v_e_5188_ = v_body_5220_;
                            v_a_5189_ = v___y_5208_;
                            v___y_5190_ = v___y_5209_;
                            v___y_5191_ = v___y_5210_;
                            v___y_5192_ = v___y_5211_;
                            v___y_5193_ = v___y_5212_;
                            v___y_5194_ = v___y_5213_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec_ref(v_body_5220_);
                            lean_dec_ref(v_f_5186_);
                            lean_dec_ref(v_p_5185_);
                            return v___x_5222_;
                        }
                    } else {
                        lean_dec_ref(v_body_5220_);
                        lean_dec_ref(v_value_5219_);
                        lean_dec_ref(v_f_5186_);
                        lean_dec_ref(v_p_5185_);
                        return v___x_5221_;
                    }
                }
                5 => {
                    v_fn_5224_ = lean_ctor_get(v_e_5188_, 0);
                    lean_inc_ref(v_fn_5224_);
                    v_arg_5225_ = lean_ctor_get(v_e_5188_, 1);
                    lean_inc_ref(v_arg_5225_);
                    lean_dec_ref_known(v_e_5188_, 2);
                    lean_inc_ref(v_f_5186_);
                    lean_inc_ref(v_p_5185_);
                    v___x_5226_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5185_, v_f_5186_, v_stopWhenVisited_5187_, v_fn_5224_, v___y_5208_, v___y_5209_, v___y_5210_, v___y_5211_, v___y_5212_, v___y_5213_);
                    if lean_obj_tag(v___x_5226_) == 0 {
                        lean_dec_ref_known(v___x_5226_, 1);
                        v_e_5188_ = v_arg_5225_;
                        v_a_5189_ = v___y_5208_;
                        v___y_5190_ = v___y_5209_;
                        v___y_5191_ = v___y_5210_;
                        v___y_5192_ = v___y_5211_;
                        v___y_5193_ = v___y_5212_;
                        v___y_5194_ = v___y_5213_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_arg_5225_);
                        lean_dec_ref(v_f_5186_);
                        lean_dec_ref(v_p_5185_);
                        return v___x_5226_;
                    }
                }
                10 => {
                    v_expr_5228_ = lean_ctor_get(v_e_5188_, 1);
                    lean_inc_ref(v_expr_5228_);
                    lean_dec_ref_known(v_e_5188_, 2);
                    v_e_5188_ = v_expr_5228_;
                    v_a_5189_ = v___y_5208_;
                    v___y_5190_ = v___y_5209_;
                    v___y_5191_ = v___y_5210_;
                    v___y_5192_ = v___y_5211_;
                    v___y_5193_ = v___y_5212_;
                    v___y_5194_ = v___y_5213_;
                    state = 0;
                    continue;
                }
                11 => {
                    v_struct_5230_ = lean_ctor_get(v_e_5188_, 2);
                    lean_inc_ref(v_struct_5230_);
                    lean_dec_ref_known(v_e_5188_, 3);
                    v_e_5188_ = v_struct_5230_;
                    v_a_5189_ = v___y_5208_;
                    v___y_5190_ = v___y_5209_;
                    v___y_5191_ = v___y_5210_;
                    v___y_5192_ = v___y_5211_;
                    v___y_5193_ = v___y_5212_;
                    v___y_5194_ = v___y_5213_;
                    state = 0;
                    continue;
                }
                _ => {
                    lean_dec_ref(v_e_5188_);
                    lean_dec_ref(v_f_5186_);
                    lean_dec_ref(v_p_5185_);
                    v___x_5232_ = lean_box(0);
                    v___x_5233_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5233_, 0, v___x_5232_);
                    return v___x_5233_;
                }
            },
            3 => {
                v___x_5239_ = (lean_unbox(v_a_5235_) as u8);
                lean_dec(v_a_5235_);
                if v___x_5239_ == 0 {
                    lean_del_object(v___x_5237_);
                    lean_inc_ref(v_p_5185_);
                    lean_inc_ref(v_e_5188_);
                    v___x_5240_ = lean_apply_1(v_p_5185_, v_e_5188_);
                    v___x_5241_ = (lean_unbox(v___x_5240_) as u8);
                    if v___x_5241_ == 0 {
                        v___y_5208_ = v_a_5189_;
                        v___y_5209_ = v___y_5190_;
                        v___y_5210_ = v___y_5191_;
                        v___y_5211_ = v___y_5192_;
                        v___y_5212_ = v___y_5193_;
                        v___y_5213_ = v___y_5194_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc_ref(v_e_5188_);
                        v___x_5242_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_5188_, v_a_5189_);
                        if lean_obj_tag(v___x_5242_) == 0 {
                            v_a_5243_ = lean_ctor_get(v___x_5242_, 0);
                            lean_inc(v_a_5243_);
                            lean_dec_ref_known(v___x_5242_, 1);
                            v___x_5244_ = (lean_unbox(v_a_5243_) as u8);
                            lean_dec(v_a_5243_);
                            if v___x_5244_ == 0 {
                                lean_inc_ref(v_f_5186_);
                                lean_inc(v___y_5194_);
                                lean_inc_ref(v___y_5193_);
                                lean_inc(v___y_5192_);
                                lean_inc_ref(v___y_5191_);
                                lean_inc(v___y_5190_);
                                lean_inc_ref(v_e_5188_);
                                v___x_5245_ = lean_apply_7(
                                    v_f_5186_,
                                    v_e_5188_,
                                    v___y_5190_,
                                    v___y_5191_,
                                    v___y_5192_,
                                    v___y_5193_,
                                    v___y_5194_,
                                    lean_box(0),
                                );
                                if lean_obj_tag(v___x_5245_) == 0 {
                                    v_isSharedCheck_5253_ = (!lean_is_exclusive(v___x_5245_)) as u8;
                                    if v_isSharedCheck_5253_ == 0 {
                                        v_unused_5254_ = lean_ctor_get(v___x_5245_, 0);
                                        lean_dec(v_unused_5254_);
                                        v___x_5247_ = v___x_5245_;
                                        v_isShared_5248_ = v_isSharedCheck_5253_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_5245_);
                                        v___x_5247_ = lean_box(0);
                                        v_isShared_5248_ = v_isSharedCheck_5253_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref(v_e_5188_);
                                    lean_dec_ref(v_f_5186_);
                                    lean_dec_ref(v_p_5185_);
                                    return v___x_5245_;
                                }
                            } else {
                                v___y_5208_ = v_a_5189_;
                                v___y_5209_ = v___y_5190_;
                                v___y_5210_ = v___y_5191_;
                                v___y_5211_ = v___y_5192_;
                                v___y_5212_ = v___y_5193_;
                                v___y_5213_ = v___y_5194_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_e_5188_);
                            lean_dec_ref(v_f_5186_);
                            lean_dec_ref(v_p_5185_);
                            v_a_5255_ = lean_ctor_get(v___x_5242_, 0);
                            v_isSharedCheck_5262_ = (!lean_is_exclusive(v___x_5242_)) as u8;
                            if v_isSharedCheck_5262_ == 0 {
                                v___x_5257_ = v___x_5242_;
                                v_isShared_5258_ = v_isSharedCheck_5262_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_5255_);
                                lean_dec(v___x_5242_);
                                v___x_5257_ = lean_box(0);
                                v_isShared_5258_ = v_isSharedCheck_5262_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_5188_);
                    lean_dec_ref(v_f_5186_);
                    lean_dec_ref(v_p_5185_);
                    v___x_5263_ = lean_box(0);
                    if v_isShared_5238_ == 0 {
                        lean_ctor_set(v___x_5237_, 0, v___x_5263_);
                        v___x_5265_ = v___x_5237_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5266_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5266_, 0, v___x_5263_);
                        v___x_5265_ = v_reuseFailAlloc_5266_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_stopWhenVisited_5187_ == 0 {
                    lean_del_object(v___x_5247_);
                    v___y_5208_ = v_a_5189_;
                    v___y_5209_ = v___y_5190_;
                    v___y_5210_ = v___y_5191_;
                    v___y_5211_ = v___y_5192_;
                    v___y_5212_ = v___y_5193_;
                    v___y_5213_ = v___y_5194_;
                    state = 2;
                    continue;
                } else {
                    lean_dec_ref(v_e_5188_);
                    lean_dec_ref(v_f_5186_);
                    lean_dec_ref(v_p_5185_);
                    v___x_5249_ = lean_box(0);
                    if v_isShared_5248_ == 0 {
                        lean_ctor_set(v___x_5247_, 0, v___x_5249_);
                        v___x_5251_ = v___x_5247_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5252_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5252_, 0, v___x_5249_);
                        v___x_5251_ = v_reuseFailAlloc_5252_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                return v___x_5251_;
            }
            6 => {
                if v_isShared_5258_ == 0 {
                    v___x_5260_ = v___x_5257_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5261_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5261_, 0, v_a_5255_);
                    v___x_5260_ = v_reuseFailAlloc_5261_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5260_;
            }
            8 => {
                return v___x_5265_;
            }
            9 => {
                if v_isShared_5271_ == 0 {
                    v___x_5273_ = v___x_5270_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
                    v___x_5273_ = v_reuseFailAlloc_5274_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3___boxed(
    mut v_p_5276_: *mut LeanObject,
    mut v_f_5277_: *mut LeanObject,
    mut v_stopWhenVisited_5278_: *mut LeanObject,
    mut v_e_5279_: *mut LeanObject,
    mut v_a_5280_: *mut LeanObject,
    mut v___y_5281_: *mut LeanObject,
    mut v___y_5282_: *mut LeanObject,
    mut v___y_5283_: *mut LeanObject,
    mut v___y_5284_: *mut LeanObject,
    mut v___y_5285_: *mut LeanObject,
    mut v___y_5286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stopWhenVisited_boxed_5287_: u8 = 0;
    let mut v_res_5288_: *mut LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_5287_ = (lean_unbox(v_stopWhenVisited_5278_) as u8);
    v_res_5288_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5276_, v_f_5277_, v_stopWhenVisited_boxed_5287_, v_e_5279_, v_a_5280_, v___y_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
    lean_dec(v___y_5285_);
    lean_dec_ref(v___y_5284_);
    lean_dec(v___y_5283_);
    lean_dec_ref(v___y_5282_);
    lean_dec(v___y_5281_);
    lean_dec(v_a_5280_);
    return v_res_5288_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(
    mut v_p_5289_: *mut LeanObject,
    mut v_f_5290_: *mut LeanObject,
    mut v_e_5291_: *mut LeanObject,
    mut v_stopWhenVisited_5292_: u8,
    mut v___y_5293_: *mut LeanObject,
    mut v___y_5294_: *mut LeanObject,
    mut v___y_5295_: *mut LeanObject,
    mut v___y_5296_: *mut LeanObject,
    mut v___y_5297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5305_: u8 = 0;
    let mut v___x_5306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5299_ = l_Lean_ForEachExprWhere_initCache;
                v___x_5300_ = lean_st_mk_ref(v___x_5299_);
                v___x_5301_ = l___private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3(v_p_5289_, v_f_5290_, v_stopWhenVisited_5292_, v_e_5291_, v___x_5300_, v___y_5293_, v___y_5294_, v___y_5295_, v___y_5296_, v___y_5297_);
                if lean_obj_tag(v___x_5301_) == 0 {
                    v_a_5302_ = lean_ctor_get(v___x_5301_, 0);
                    v_isSharedCheck_5310_ = (!lean_is_exclusive(v___x_5301_)) as u8;
                    if v_isSharedCheck_5310_ == 0 {
                        v___x_5304_ = v___x_5301_;
                        v_isShared_5305_ = v_isSharedCheck_5310_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5302_);
                        lean_dec(v___x_5301_);
                        v___x_5304_ = lean_box(0);
                        v_isShared_5305_ = v_isSharedCheck_5310_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5300_);
                    return v___x_5301_;
                }
            }
            1 => {
                v___x_5306_ = lean_st_ref_get(v___x_5300_);
                lean_dec(v___x_5300_);
                lean_dec(v___x_5306_);
                if v_isShared_5305_ == 0 {
                    v___x_5308_ = v___x_5304_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5309_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5309_, 0, v_a_5302_);
                    v___x_5308_ = v_reuseFailAlloc_5309_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1___boxed(
    mut v_p_5311_: *mut LeanObject,
    mut v_f_5312_: *mut LeanObject,
    mut v_e_5313_: *mut LeanObject,
    mut v_stopWhenVisited_5314_: *mut LeanObject,
    mut v___y_5315_: *mut LeanObject,
    mut v___y_5316_: *mut LeanObject,
    mut v___y_5317_: *mut LeanObject,
    mut v___y_5318_: *mut LeanObject,
    mut v___y_5319_: *mut LeanObject,
    mut v___y_5320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_stopWhenVisited_boxed_5321_: u8 = 0;
    let mut v_res_5322_: *mut LeanObject = core::ptr::null_mut();
    v_stopWhenVisited_boxed_5321_ = (lean_unbox(v_stopWhenVisited_5314_) as u8);
    v_res_5322_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(
        v_p_5311_,
        v_f_5312_,
        v_e_5313_,
        v_stopWhenVisited_boxed_5321_,
        v___y_5315_,
        v___y_5316_,
        v___y_5317_,
        v___y_5318_,
        v___y_5319_,
    );
    lean_dec(v___y_5319_);
    lean_dec_ref(v___y_5318_);
    lean_dec(v___y_5317_);
    lean_dec_ref(v___y_5316_);
    lean_dec(v___y_5315_);
    return v_res_5322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(
    mut v___f_5324_: *mut LeanObject,
    mut v___f_5325_: *mut LeanObject,
    mut v___x_5326_: u8,
    mut v_e_5327_: *mut LeanObject,
    mut v_candidates_5328_: *mut LeanObject,
    mut v___y_5329_: *mut LeanObject,
    mut v___y_5330_: *mut LeanObject,
    mut v___y_5331_: *mut LeanObject,
    mut v___y_5332_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5342_: u8 = 0;
    let mut v___x_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5347_: u8 = 0;
    let mut v___x_5348_: u8 = 0;
    let mut v___x_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5358_: u8 = 0;
    let mut v___x_5360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5362_: u8 = 0;
    let mut v_a_5363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5366_: u8 = 0;
    let mut v___x_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5334_ =
                    l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(
                        v_e_5327_,
                        v___y_5330_,
                    );
                if lean_obj_tag(v___x_5334_) == 0 {
                    v_a_5335_ = lean_ctor_get(v___x_5334_, 0);
                    lean_inc(v_a_5335_);
                    lean_dec_ref_known(v___x_5334_, 1);
                    v___x_5336_ = lean_st_mk_ref(v_candidates_5328_);
                    v___x_5348_ = l_Lean_Expr_hasFVar(v_a_5335_);
                    if v___x_5348_ == 0 {
                        lean_dec(v_a_5335_);
                        lean_dec_ref(v___f_5325_);
                        v___x_5349_ = lean_box(0);
                        lean_inc(v___y_5332_);
                        lean_inc_ref(v___y_5331_);
                        lean_inc(v___y_5330_);
                        lean_inc_ref(v___y_5329_);
                        lean_inc(v___x_5336_);
                        v___x_5350_ = lean_apply_7(
                            v___f_5324_,
                            v___x_5349_,
                            v___x_5336_,
                            v___y_5329_,
                            v___y_5330_,
                            v___y_5331_,
                            v___y_5332_,
                            lean_box(0),
                        );
                        v___y_5338_ = v___x_5350_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0;
                        v___x_5352_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_5351_, v___f_5325_, v_a_5335_, v___x_5326_, v___x_5336_, v___y_5329_, v___y_5330_, v___y_5331_, v___y_5332_);
                        if lean_obj_tag(v___x_5352_) == 0 {
                            v_a_5353_ = lean_ctor_get(v___x_5352_, 0);
                            lean_inc(v_a_5353_);
                            lean_dec_ref_known(v___x_5352_, 1);
                            lean_inc(v___y_5332_);
                            lean_inc_ref(v___y_5331_);
                            lean_inc(v___y_5330_);
                            lean_inc_ref(v___y_5329_);
                            lean_inc(v___x_5336_);
                            v___x_5354_ = lean_apply_7(
                                v___f_5324_,
                                v_a_5353_,
                                v___x_5336_,
                                v___y_5329_,
                                v___y_5330_,
                                v___y_5331_,
                                v___y_5332_,
                                lean_box(0),
                            );
                            v___y_5338_ = v___x_5354_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_5336_);
                            lean_dec_ref(v___f_5324_);
                            v_a_5355_ = lean_ctor_get(v___x_5352_, 0);
                            v_isSharedCheck_5362_ = (!lean_is_exclusive(v___x_5352_)) as u8;
                            if v_isSharedCheck_5362_ == 0 {
                                v___x_5357_ = v___x_5352_;
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_5355_);
                                lean_dec(v___x_5352_);
                                v___x_5357_ = lean_box(0);
                                v_isShared_5358_ = v_isSharedCheck_5362_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_candidates_5328_);
                    lean_dec_ref(v___f_5325_);
                    lean_dec_ref(v___f_5324_);
                    v_a_5363_ = lean_ctor_get(v___x_5334_, 0);
                    v_isSharedCheck_5370_ = (!lean_is_exclusive(v___x_5334_)) as u8;
                    if v_isSharedCheck_5370_ == 0 {
                        v___x_5365_ = v___x_5334_;
                        v_isShared_5366_ = v_isSharedCheck_5370_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5363_);
                        lean_dec(v___x_5334_);
                        v___x_5365_ = lean_box(0);
                        v_isShared_5366_ = v_isSharedCheck_5370_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_5338_) == 0 {
                    v_a_5339_ = lean_ctor_get(v___y_5338_, 0);
                    v_isSharedCheck_5347_ = (!lean_is_exclusive(v___y_5338_)) as u8;
                    if v_isSharedCheck_5347_ == 0 {
                        v___x_5341_ = v___y_5338_;
                        v_isShared_5342_ = v_isSharedCheck_5347_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5339_);
                        lean_dec(v___y_5338_);
                        v___x_5341_ = lean_box(0);
                        v_isShared_5342_ = v_isSharedCheck_5347_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5336_);
                    return v___y_5338_;
                }
            }
            2 => {
                v___x_5343_ = lean_st_ref_get(v___x_5336_);
                lean_dec(v___x_5336_);
                lean_dec(v___x_5343_);
                if v_isShared_5342_ == 0 {
                    v___x_5345_ = v___x_5341_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5346_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5346_, 0, v_a_5339_);
                    v___x_5345_ = v_reuseFailAlloc_5346_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5345_;
            }
            4 => {
                if v_isShared_5358_ == 0 {
                    v___x_5360_ = v___x_5357_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5361_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_a_5355_);
                    v___x_5360_ = v_reuseFailAlloc_5361_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5360_;
            }
            6 => {
                if v_isShared_5366_ == 0 {
                    v___x_5368_ = v___x_5365_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5369_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5369_, 0, v_a_5363_);
                    v___x_5368_ = v_reuseFailAlloc_5369_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___boxed(
    mut v___f_5371_: *mut LeanObject,
    mut v___f_5372_: *mut LeanObject,
    mut v___x_5373_: *mut LeanObject,
    mut v_e_5374_: *mut LeanObject,
    mut v_candidates_5375_: *mut LeanObject,
    mut v___y_5376_: *mut LeanObject,
    mut v___y_5377_: *mut LeanObject,
    mut v___y_5378_: *mut LeanObject,
    mut v___y_5379_: *mut LeanObject,
    mut v___y_5380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_17597__boxed_5381_: u8 = 0;
    let mut v_res_5382_: *mut LeanObject = core::ptr::null_mut();
    v___x_17597__boxed_5381_ = (lean_unbox(v___x_5373_) as u8);
    v_res_5382_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5371_, v___f_5372_, v___x_17597__boxed_5381_, v_e_5374_, v_candidates_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_);
    lean_dec(v___y_5379_);
    lean_dec_ref(v___y_5378_);
    lean_dec(v___y_5377_);
    lean_dec_ref(v___y_5376_);
    return v_res_5382_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(
    mut v_e_5383_: *mut LeanObject,
    mut v___y_5384_: *mut LeanObject,
    mut v___y_5385_: *mut LeanObject,
    mut v___y_5386_: *mut LeanObject,
    mut v___y_5387_: *mut LeanObject,
    mut v___y_5388_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    v___x_5390_ = lean_st_ref_take(v___y_5384_);
    v___x_5391_ = l_Lean_Expr_fvarId_x21(v_e_5383_);
    v___x_5392_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v___x_5390_, v___x_5391_);
    lean_dec(v___x_5391_);
    v___x_5393_ = lean_st_ref_set(v___y_5384_, v___x_5392_);
    v___x_5394_ = lean_box(0);
    v___x_5395_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5395_, 0, v___x_5394_);
    return v___x_5395_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0___boxed(
    mut v_e_5396_: *mut LeanObject,
    mut v___y_5397_: *mut LeanObject,
    mut v___y_5398_: *mut LeanObject,
    mut v___y_5399_: *mut LeanObject,
    mut v___y_5400_: *mut LeanObject,
    mut v___y_5401_: *mut LeanObject,
    mut v___y_5402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5403_: *mut LeanObject = core::ptr::null_mut();
    v_res_5403_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__0(v_e_5396_, v___y_5397_, v___y_5398_, v___y_5399_, v___y_5400_, v___y_5401_);
    lean_dec(v___y_5401_);
    lean_dec_ref(v___y_5400_);
    lean_dec(v___y_5399_);
    lean_dec_ref(v___y_5398_);
    lean_dec(v___y_5397_);
    lean_dec_ref(v_e_5396_);
    return v_res_5403_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(
    mut v_____r_5404_: *mut LeanObject,
    mut v___y_5405_: *mut LeanObject,
    mut v___y_5406_: *mut LeanObject,
    mut v___y_5407_: *mut LeanObject,
    mut v___y_5408_: *mut LeanObject,
    mut v___y_5409_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut LeanObject = core::ptr::null_mut();
    v___x_5411_ = lean_st_ref_get(v___y_5405_);
    v___x_5412_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_5412_, 0, v___x_5411_);
    return v___x_5412_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1___boxed(
    mut v_____r_5413_: *mut LeanObject,
    mut v___y_5414_: *mut LeanObject,
    mut v___y_5415_: *mut LeanObject,
    mut v___y_5416_: *mut LeanObject,
    mut v___y_5417_: *mut LeanObject,
    mut v___y_5418_: *mut LeanObject,
    mut v___y_5419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5420_: *mut LeanObject = core::ptr::null_mut();
    v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__1(v_____r_5413_, v___y_5414_, v___y_5415_, v___y_5416_, v___y_5417_, v___y_5418_);
    lean_dec(v___y_5418_);
    lean_dec_ref(v___y_5417_);
    lean_dec(v___y_5416_);
    lean_dec_ref(v___y_5415_);
    lean_dec(v___y_5414_);
    return v_res_5420_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(
    mut v_x_5421_: *mut LeanObject,
    mut v_x_5422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5428_: u8 = 0;
    let mut v___x_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: u64 = 0;
    let mut v___x_5431_: u64 = 0;
    let mut v___x_5432_: u64 = 0;
    let mut v_fold_5433_: u64 = 0;
    let mut v___x_5434_: u64 = 0;
    let mut v___x_5435_: u64 = 0;
    let mut v___x_5436_: u64 = 0;
    let mut v___x_5437_: usize = 0;
    let mut v___x_5438_: usize = 0;
    let mut v___x_5439_: usize = 0;
    let mut v___x_5440_: usize = 0;
    let mut v___x_5441_: usize = 0;
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5448_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_5422_) == 0 {
                    return v_x_5421_;
                } else {
                    v_key_5423_ = lean_ctor_get(v_x_5422_, 0);
                    v_value_5424_ = lean_ctor_get(v_x_5422_, 1);
                    v_tail_5425_ = lean_ctor_get(v_x_5422_, 2);
                    v_isSharedCheck_5448_ = (!lean_is_exclusive(v_x_5422_)) as u8;
                    if v_isSharedCheck_5448_ == 0 {
                        v___x_5427_ = v_x_5422_;
                        v_isShared_5428_ = v_isSharedCheck_5448_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_5425_);
                        lean_inc(v_value_5424_);
                        lean_inc(v_key_5423_);
                        lean_dec(v_x_5422_);
                        v___x_5427_ = lean_box(0);
                        v_isShared_5428_ = v_isSharedCheck_5448_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5429_ = lean_array_get_size(v_x_5421_);
                v___x_5430_ = l_Lean_instHashableFVarId_hash(v_key_5423_);
                v___x_5431_ = 32u64;
                v___x_5432_ = lean_uint64_shift_right(v___x_5430_, v___x_5431_);
                v_fold_5433_ = lean_uint64_xor(v___x_5430_, v___x_5432_);
                v___x_5434_ = 16u64;
                v___x_5435_ = lean_uint64_shift_right(v_fold_5433_, v___x_5434_);
                v___x_5436_ = lean_uint64_xor(v_fold_5433_, v___x_5435_);
                v___x_5437_ = lean_uint64_to_usize(v___x_5436_);
                v___x_5438_ = lean_usize_of_nat(v___x_5429_);
                v___x_5439_ = 1usize;
                v___x_5440_ = lean_usize_sub(v___x_5438_, v___x_5439_);
                v___x_5441_ = lean_usize_land(v___x_5437_, v___x_5440_);
                v___x_5442_ = lean_array_uget_borrowed(v_x_5421_, v___x_5441_);
                lean_inc(v___x_5442_);
                if v_isShared_5428_ == 0 {
                    lean_ctor_set(v___x_5427_, 2, v___x_5442_);
                    v___x_5444_ = v___x_5427_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5447_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_key_5423_);
                    lean_ctor_set(v_reuseFailAlloc_5447_, 1, v_value_5424_);
                    lean_ctor_set(v_reuseFailAlloc_5447_, 2, v___x_5442_);
                    v___x_5444_ = v_reuseFailAlloc_5447_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5445_ = lean_array_uset(v_x_5421_, v___x_5441_, v___x_5444_);
                v_x_5421_ = v___x_5445_;
                v_x_5422_ = v_tail_5425_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(
    mut v_i_5449_: *mut LeanObject,
    mut v_source_5450_: *mut LeanObject,
    mut v_target_5451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: u8 = 0;
    let mut v_es_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5459_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5452_ = lean_array_get_size(v_source_5450_);
                v___x_5453_ = lean_nat_dec_lt(v_i_5449_, v___x_5452_);
                if v___x_5453_ == 0 {
                    lean_dec_ref(v_source_5450_);
                    lean_dec(v_i_5449_);
                    return v_target_5451_;
                } else {
                    v_es_5454_ = lean_array_fget(v_source_5450_, v_i_5449_);
                    v___x_5455_ = lean_box(0);
                    v_source_5456_ = lean_array_fset(v_source_5450_, v_i_5449_, v___x_5455_);
                    v_target_5457_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_target_5451_, v_es_5454_);
                    v___x_5458_ = lean_unsigned_to_nat(1);
                    v___x_5459_ = lean_nat_add(v_i_5449_, v___x_5458_);
                    lean_dec(v_i_5449_);
                    v_i_5449_ = v___x_5459_;
                    v_source_5450_ = v_source_5456_;
                    v_target_5451_ = v_target_5457_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(
    mut v_data_5461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5468_: *mut LeanObject = core::ptr::null_mut();
    v___x_5462_ = lean_array_get_size(v_data_5461_);
    v___x_5463_ = lean_unsigned_to_nat(2);
    v_nbuckets_5464_ = lean_nat_mul(v___x_5462_, v___x_5463_);
    v___x_5465_ = lean_unsigned_to_nat(0);
    v___x_5466_ = lean_box(0);
    v___x_5467_ = lean_mk_array(v_nbuckets_5464_, v___x_5466_);
    v___x_5468_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v___x_5465_, v_data_5461_, v___x_5467_);
    return v___x_5468_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(
    mut v_m_5469_: *mut LeanObject,
    mut v_a_5470_: *mut LeanObject,
    mut v_b_5471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_5472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_5473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5475_: u64 = 0;
    let mut v___x_5476_: u64 = 0;
    let mut v___x_5477_: u64 = 0;
    let mut v_fold_5478_: u64 = 0;
    let mut v___x_5479_: u64 = 0;
    let mut v___x_5480_: u64 = 0;
    let mut v___x_5481_: u64 = 0;
    let mut v___x_5482_: usize = 0;
    let mut v___x_5483_: usize = 0;
    let mut v___x_5484_: usize = 0;
    let mut v___x_5485_: usize = 0;
    let mut v___x_5486_: usize = 0;
    let mut v_bkt_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5488_: u8 = 0;
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5491_: u8 = 0;
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: u8 = 0;
    let mut v_val_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5509_: u8 = 0;
    let mut v_unused_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5511_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5472_ = lean_ctor_get(v_m_5469_, 0);
                v_buckets_5473_ = lean_ctor_get(v_m_5469_, 1);
                v___x_5474_ = lean_array_get_size(v_buckets_5473_);
                v___x_5475_ = l_Lean_instHashableFVarId_hash(v_a_5470_);
                v___x_5476_ = 32u64;
                v___x_5477_ = lean_uint64_shift_right(v___x_5475_, v___x_5476_);
                v_fold_5478_ = lean_uint64_xor(v___x_5475_, v___x_5477_);
                v___x_5479_ = 16u64;
                v___x_5480_ = lean_uint64_shift_right(v_fold_5478_, v___x_5479_);
                v___x_5481_ = lean_uint64_xor(v_fold_5478_, v___x_5480_);
                v___x_5482_ = lean_uint64_to_usize(v___x_5481_);
                v___x_5483_ = lean_usize_of_nat(v___x_5474_);
                v___x_5484_ = 1usize;
                v___x_5485_ = lean_usize_sub(v___x_5483_, v___x_5484_);
                v___x_5486_ = lean_usize_land(v___x_5482_, v___x_5485_);
                v_bkt_5487_ = lean_array_uget_borrowed(v_buckets_5473_, v___x_5486_);
                v___x_5488_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_5470_, v_bkt_5487_);
                if v___x_5488_ == 0 {
                    lean_inc_ref(v_buckets_5473_);
                    lean_inc(v_size_5472_);
                    v_isSharedCheck_5509_ = (!lean_is_exclusive(v_m_5469_)) as u8;
                    if v_isSharedCheck_5509_ == 0 {
                        v_unused_5510_ = lean_ctor_get(v_m_5469_, 1);
                        lean_dec(v_unused_5510_);
                        v_unused_5511_ = lean_ctor_get(v_m_5469_, 0);
                        lean_dec(v_unused_5511_);
                        v___x_5490_ = v_m_5469_;
                        v_isShared_5491_ = v_isSharedCheck_5509_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_m_5469_);
                        v___x_5490_ = lean_box(0);
                        v_isShared_5491_ = v_isSharedCheck_5509_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_b_5471_);
                    lean_dec(v_a_5470_);
                    return v_m_5469_;
                }
            }
            1 => {
                v___x_5492_ = lean_unsigned_to_nat(1);
                v_size_x27_5493_ = lean_nat_add(v_size_5472_, v___x_5492_);
                lean_dec(v_size_5472_);
                lean_inc(v_bkt_5487_);
                v___x_5494_ = lean_alloc_ctor(1, 3, (0) as u32);
                lean_ctor_set(v___x_5494_, 0, v_a_5470_);
                lean_ctor_set(v___x_5494_, 1, v_b_5471_);
                lean_ctor_set(v___x_5494_, 2, v_bkt_5487_);
                v_buckets_x27_5495_ = lean_array_uset(v_buckets_5473_, v___x_5486_, v___x_5494_);
                v___x_5496_ = lean_unsigned_to_nat(4);
                v___x_5497_ = lean_nat_mul(v_size_x27_5493_, v___x_5496_);
                v___x_5498_ = lean_unsigned_to_nat(3);
                v___x_5499_ = lean_nat_div(v___x_5497_, v___x_5498_);
                lean_dec(v___x_5497_);
                v___x_5500_ = lean_array_get_size(v_buckets_x27_5495_);
                v___x_5501_ = lean_nat_dec_le(v___x_5499_, v___x_5500_);
                lean_dec(v___x_5499_);
                if v___x_5501_ == 0 {
                    v_val_5502_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_buckets_x27_5495_);
                    if v_isShared_5491_ == 0 {
                        lean_ctor_set(v___x_5490_, 1, v_val_5502_);
                        lean_ctor_set(v___x_5490_, 0, v_size_x27_5493_);
                        v___x_5504_ = v___x_5490_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5505_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_size_x27_5493_);
                        lean_ctor_set(v_reuseFailAlloc_5505_, 1, v_val_5502_);
                        v___x_5504_ = v_reuseFailAlloc_5505_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_5491_ == 0 {
                        lean_ctor_set(v___x_5490_, 1, v_buckets_x27_5495_);
                        lean_ctor_set(v___x_5490_, 0, v_size_x27_5493_);
                        v___x_5507_ = v___x_5490_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5508_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5508_, 0, v_size_x27_5493_);
                        lean_ctor_set(v_reuseFailAlloc_5508_, 1, v_buckets_x27_5495_);
                        v___x_5507_ = v_reuseFailAlloc_5508_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5504_;
            }
            3 => {
                return v___x_5507_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(
    mut v_as_5514_: *mut LeanObject,
    mut v_sz_5515_: usize,
    mut v_i_5516_: usize,
    mut v_b_5517_: *mut LeanObject,
    mut v___y_5518_: *mut LeanObject,
    mut v___y_5519_: *mut LeanObject,
    mut v___y_5520_: *mut LeanObject,
    mut v___y_5521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5523_: u8 = 0;
    let mut v___x_5524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5528_: u8 = 0;
    let mut v___x_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: usize = 0;
    let mut v___x_5535_: usize = 0;
    let mut v_reuseFailAlloc_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5545_: u8 = 0;
    let mut v___f_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_candidates_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5557_: u8 = 0;
    let mut v___x_5558_: u8 = 0;
    let mut v_a_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5562_: u8 = 0;
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5566_: u8 = 0;
    let mut v___x_5567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5576_: u8 = 0;
    let mut v___x_5578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5580_: u8 = 0;
    let mut v_a_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5584_: u8 = 0;
    let mut v___x_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5588_: u8 = 0;
    let mut v_isSharedCheck_5589_: u8 = 0;
    let mut v_unused_5590_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5523_ = lean_usize_dec_lt(v_i_5516_, v_sz_5515_);
                if v___x_5523_ == 0 {
                    v___x_5524_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5524_, 0, v_b_5517_);
                    return v___x_5524_;
                } else {
                    v_snd_5525_ = lean_ctor_get(v_b_5517_, 1);
                    v_isSharedCheck_5589_ = (!lean_is_exclusive(v_b_5517_)) as u8;
                    if v_isSharedCheck_5589_ == 0 {
                        v_unused_5590_ = lean_ctor_get(v_b_5517_, 0);
                        lean_dec(v_unused_5590_);
                        v___x_5527_ = v_b_5517_;
                        v_isShared_5528_ = v_isSharedCheck_5589_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5525_);
                        lean_dec(v_b_5517_);
                        v___x_5527_ = lean_box(0);
                        v_isShared_5528_ = v_isSharedCheck_5589_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5529_ = lean_box(0);
                v_a_5538_ = lean_array_uget_borrowed(v_as_5514_, v_i_5516_);
                if lean_obj_tag(v_a_5538_) == 0 {
                    v_a_5531_ = v_snd_5525_;
                    state = 2;
                    continue;
                } else {
                    v_val_5539_ = lean_ctor_get(v_a_5538_, 0);
                    v___x_5545_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5539_);
                    if v___x_5545_ == 0 {
                        v___f_5546_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5548_ = l_Lean_LocalDecl_type(v_val_5539_);
                        lean_inc_ref(v___x_5548_);
                        v___x_5567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5547_, v___f_5546_, v___x_5545_, v___x_5548_, v_snd_5525_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
                        if lean_obj_tag(v___x_5567_) == 0 {
                            v_a_5568_ = lean_ctor_get(v___x_5567_, 0);
                            lean_inc(v_a_5568_);
                            lean_dec_ref_known(v___x_5567_, 1);
                            v___x_5569_ = l_Lean_LocalDecl_value_x3f(v_val_5539_, v___x_5545_);
                            if lean_obj_tag(v___x_5569_) == 0 {
                                v_candidates_5550_ = v_a_5568_;
                                v___y_5551_ = v___y_5518_;
                                v___y_5552_ = v___y_5519_;
                                v___y_5553_ = v___y_5520_;
                                v___y_5554_ = v___y_5521_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5570_ = lean_ctor_get(v___x_5569_, 0);
                                lean_inc(v_val_5570_);
                                lean_dec_ref_known(v___x_5569_, 1);
                                v___x_5571_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5547_, v___f_5546_, v___x_5545_, v_val_5570_, v_a_5568_, v___y_5518_, v___y_5519_, v___y_5520_, v___y_5521_);
                                if lean_obj_tag(v___x_5571_) == 0 {
                                    v_a_5572_ = lean_ctor_get(v___x_5571_, 0);
                                    lean_inc(v_a_5572_);
                                    lean_dec_ref_known(v___x_5571_, 1);
                                    v_candidates_5550_ = v_a_5572_;
                                    v___y_5551_ = v___y_5518_;
                                    v___y_5552_ = v___y_5519_;
                                    v___y_5553_ = v___y_5520_;
                                    v___y_5554_ = v___y_5521_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec_ref(v___x_5548_);
                                    lean_del_object(v___x_5527_);
                                    v_a_5573_ = lean_ctor_get(v___x_5571_, 0);
                                    v_isSharedCheck_5580_ = (!lean_is_exclusive(v___x_5571_)) as u8;
                                    if v_isSharedCheck_5580_ == 0 {
                                        v___x_5575_ = v___x_5571_;
                                        v_isShared_5576_ = v_isSharedCheck_5580_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5573_);
                                        lean_dec(v___x_5571_);
                                        v___x_5575_ = lean_box(0);
                                        v_isShared_5576_ = v_isSharedCheck_5580_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_5548_);
                            lean_del_object(v___x_5527_);
                            v_a_5581_ = lean_ctor_get(v___x_5567_, 0);
                            v_isSharedCheck_5588_ = (!lean_is_exclusive(v___x_5567_)) as u8;
                            if v_isSharedCheck_5588_ == 0 {
                                v___x_5583_ = v___x_5567_;
                                v_isShared_5584_ = v_isSharedCheck_5588_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_5581_);
                                lean_dec(v___x_5567_);
                                v___x_5583_ = lean_box(0);
                                v_isShared_5584_ = v_isSharedCheck_5588_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_a_5531_ = v_snd_5525_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5528_ == 0 {
                    lean_ctor_set(v___x_5527_, 1, v_a_5531_);
                    lean_ctor_set(v___x_5527_, 0, v___x_5529_);
                    v___x_5533_ = v___x_5527_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5537_, 0, v___x_5529_);
                    lean_ctor_set(v_reuseFailAlloc_5537_, 1, v_a_5531_);
                    v___x_5533_ = v_reuseFailAlloc_5537_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5534_ = 1usize;
                v___x_5535_ = lean_usize_add(v_i_5516_, v___x_5534_);
                v_i_5516_ = v___x_5535_;
                v_b_5517_ = v___x_5533_;
                state = 0;
                continue;
            }
            4 => {
                v___x_5542_ = l_Lean_LocalDecl_fvarId(v_val_5539_);
                v___x_5543_ = lean_box(0);
                v___x_5544_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_5541_, v___x_5542_, v___x_5543_);
                v_a_5531_ = v___x_5544_;
                state = 2;
                continue;
            }
            5 => {
                v___x_5555_ = l_Lean_Meta_isProp(
                    v___x_5548_,
                    v___y_5551_,
                    v___y_5552_,
                    v___y_5553_,
                    v___y_5554_,
                );
                if lean_obj_tag(v___x_5555_) == 0 {
                    v_a_5556_ = lean_ctor_get(v___x_5555_, 0);
                    lean_inc(v_a_5556_);
                    lean_dec_ref_known(v___x_5555_, 1);
                    v___x_5557_ = (lean_unbox(v_a_5556_) as u8);
                    lean_dec(v_a_5556_);
                    if v___x_5557_ == 0 {
                        v_a_5531_ = v_candidates_5550_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5558_ = l_Lean_LocalDecl_hasValue(v_val_5539_, v___x_5545_);
                        if v___x_5558_ == 0 {
                            v___y_5541_ = v_candidates_5550_;
                            state = 4;
                            continue;
                        } else {
                            if v___x_5545_ == 0 {
                                v_a_5531_ = v_candidates_5550_;
                                state = 2;
                                continue;
                            } else {
                                v___y_5541_ = v_candidates_5550_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_candidates_5550_);
                    lean_del_object(v___x_5527_);
                    v_a_5559_ = lean_ctor_get(v___x_5555_, 0);
                    v_isSharedCheck_5566_ = (!lean_is_exclusive(v___x_5555_)) as u8;
                    if v_isSharedCheck_5566_ == 0 {
                        v___x_5561_ = v___x_5555_;
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5559_);
                        lean_dec(v___x_5555_);
                        v___x_5561_ = lean_box(0);
                        v_isShared_5562_ = v_isSharedCheck_5566_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5562_ == 0 {
                    v___x_5564_ = v___x_5561_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5565_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5565_, 0, v_a_5559_);
                    v___x_5564_ = v_reuseFailAlloc_5565_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5564_;
            }
            8 => {
                if v_isShared_5576_ == 0 {
                    v___x_5578_ = v___x_5575_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_a_5573_);
                    v___x_5578_ = v_reuseFailAlloc_5579_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5578_;
            }
            10 => {
                if v_isShared_5584_ == 0 {
                    v___x_5586_ = v___x_5583_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5587_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5587_, 0, v_a_5581_);
                    v___x_5586_ = v_reuseFailAlloc_5587_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5586_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___boxed(
    mut v_as_5591_: *mut LeanObject,
    mut v_sz_5592_: *mut LeanObject,
    mut v_i_5593_: *mut LeanObject,
    mut v_b_5594_: *mut LeanObject,
    mut v___y_5595_: *mut LeanObject,
    mut v___y_5596_: *mut LeanObject,
    mut v___y_5597_: *mut LeanObject,
    mut v___y_5598_: *mut LeanObject,
    mut v___y_5599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5600_: usize = 0;
    let mut v_i_boxed_5601_: usize = 0;
    let mut v_res_5602_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5600_ = lean_unbox_usize(v_sz_5592_);
    lean_dec(v_sz_5592_);
    v_i_boxed_5601_ = lean_unbox_usize(v_i_5593_);
    lean_dec(v_i_5593_);
    v_res_5602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_5591_, v_sz_boxed_5600_, v_i_boxed_5601_, v_b_5594_, v___y_5595_, v___y_5596_, v___y_5597_, v___y_5598_);
    lean_dec(v___y_5598_);
    lean_dec_ref(v___y_5597_);
    lean_dec(v___y_5596_);
    lean_dec_ref(v___y_5595_);
    lean_dec_ref(v_as_5591_);
    return v_res_5602_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(
    mut v_as_5603_: *mut LeanObject,
    mut v_sz_5604_: usize,
    mut v_i_5605_: usize,
    mut v_b_5606_: *mut LeanObject,
    mut v___y_5607_: *mut LeanObject,
    mut v___y_5608_: *mut LeanObject,
    mut v___y_5609_: *mut LeanObject,
    mut v___y_5610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5612_: u8 = 0;
    let mut v___x_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5617_: u8 = 0;
    let mut v___x_5618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5623_: usize = 0;
    let mut v___x_5624_: usize = 0;
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5634_: u8 = 0;
    let mut v___f_5635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_candidates_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5646_: u8 = 0;
    let mut v___x_5647_: u8 = 0;
    let mut v_a_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5651_: u8 = 0;
    let mut v___x_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5655_: u8 = 0;
    let mut v___x_5656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5665_: u8 = 0;
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5669_: u8 = 0;
    let mut v_a_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5673_: u8 = 0;
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5677_: u8 = 0;
    let mut v_isSharedCheck_5678_: u8 = 0;
    let mut v_unused_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5612_ = lean_usize_dec_lt(v_i_5605_, v_sz_5604_);
                if v___x_5612_ == 0 {
                    v___x_5613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5613_, 0, v_b_5606_);
                    return v___x_5613_;
                } else {
                    v_snd_5614_ = lean_ctor_get(v_b_5606_, 1);
                    v_isSharedCheck_5678_ = (!lean_is_exclusive(v_b_5606_)) as u8;
                    if v_isSharedCheck_5678_ == 0 {
                        v_unused_5679_ = lean_ctor_get(v_b_5606_, 0);
                        lean_dec(v_unused_5679_);
                        v___x_5616_ = v_b_5606_;
                        v_isShared_5617_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5614_);
                        lean_dec(v_b_5606_);
                        v___x_5616_ = lean_box(0);
                        v_isShared_5617_ = v_isSharedCheck_5678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5618_ = lean_box(0);
                v_a_5627_ = lean_array_uget_borrowed(v_as_5603_, v_i_5605_);
                if lean_obj_tag(v_a_5627_) == 0 {
                    v_a_5620_ = v_snd_5614_;
                    state = 2;
                    continue;
                } else {
                    v_val_5628_ = lean_ctor_get(v_a_5627_, 0);
                    v___x_5634_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5628_);
                    if v___x_5634_ == 0 {
                        v___f_5635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5636_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5637_ = l_Lean_LocalDecl_type(v_val_5628_);
                        lean_inc_ref(v___x_5637_);
                        v___x_5656_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5636_, v___f_5635_, v___x_5634_, v___x_5637_, v_snd_5614_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
                        if lean_obj_tag(v___x_5656_) == 0 {
                            v_a_5657_ = lean_ctor_get(v___x_5656_, 0);
                            lean_inc(v_a_5657_);
                            lean_dec_ref_known(v___x_5656_, 1);
                            v___x_5658_ = l_Lean_LocalDecl_value_x3f(v_val_5628_, v___x_5634_);
                            if lean_obj_tag(v___x_5658_) == 0 {
                                v_candidates_5639_ = v_a_5657_;
                                v___y_5640_ = v___y_5607_;
                                v___y_5641_ = v___y_5608_;
                                v___y_5642_ = v___y_5609_;
                                v___y_5643_ = v___y_5610_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5659_ = lean_ctor_get(v___x_5658_, 0);
                                lean_inc(v_val_5659_);
                                lean_dec_ref_known(v___x_5658_, 1);
                                v___x_5660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5636_, v___f_5635_, v___x_5634_, v_val_5659_, v_a_5657_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
                                if lean_obj_tag(v___x_5660_) == 0 {
                                    v_a_5661_ = lean_ctor_get(v___x_5660_, 0);
                                    lean_inc(v_a_5661_);
                                    lean_dec_ref_known(v___x_5660_, 1);
                                    v_candidates_5639_ = v_a_5661_;
                                    v___y_5640_ = v___y_5607_;
                                    v___y_5641_ = v___y_5608_;
                                    v___y_5642_ = v___y_5609_;
                                    v___y_5643_ = v___y_5610_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec_ref(v___x_5637_);
                                    lean_del_object(v___x_5616_);
                                    v_a_5662_ = lean_ctor_get(v___x_5660_, 0);
                                    v_isSharedCheck_5669_ = (!lean_is_exclusive(v___x_5660_)) as u8;
                                    if v_isSharedCheck_5669_ == 0 {
                                        v___x_5664_ = v___x_5660_;
                                        v_isShared_5665_ = v_isSharedCheck_5669_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5662_);
                                        lean_dec(v___x_5660_);
                                        v___x_5664_ = lean_box(0);
                                        v_isShared_5665_ = v_isSharedCheck_5669_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_5637_);
                            lean_del_object(v___x_5616_);
                            v_a_5670_ = lean_ctor_get(v___x_5656_, 0);
                            v_isSharedCheck_5677_ = (!lean_is_exclusive(v___x_5656_)) as u8;
                            if v_isSharedCheck_5677_ == 0 {
                                v___x_5672_ = v___x_5656_;
                                v_isShared_5673_ = v_isSharedCheck_5677_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_5670_);
                                lean_dec(v___x_5656_);
                                v___x_5672_ = lean_box(0);
                                v_isShared_5673_ = v_isSharedCheck_5677_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_a_5620_ = v_snd_5614_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5617_ == 0 {
                    lean_ctor_set(v___x_5616_, 1, v_a_5620_);
                    lean_ctor_set(v___x_5616_, 0, v___x_5618_);
                    v___x_5622_ = v___x_5616_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5626_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5626_, 0, v___x_5618_);
                    lean_ctor_set(v_reuseFailAlloc_5626_, 1, v_a_5620_);
                    v___x_5622_ = v_reuseFailAlloc_5626_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5623_ = 1usize;
                v___x_5624_ = lean_usize_add(v_i_5605_, v___x_5623_);
                v___x_5625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14(v_as_5603_, v_sz_5604_, v___x_5624_, v___x_5622_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
                return v___x_5625_;
            }
            4 => {
                v___x_5631_ = l_Lean_LocalDecl_fvarId(v_val_5628_);
                v___x_5632_ = lean_box(0);
                v___x_5633_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_5630_, v___x_5631_, v___x_5632_);
                v_a_5620_ = v___x_5633_;
                state = 2;
                continue;
            }
            5 => {
                v___x_5644_ = l_Lean_Meta_isProp(
                    v___x_5637_,
                    v___y_5640_,
                    v___y_5641_,
                    v___y_5642_,
                    v___y_5643_,
                );
                if lean_obj_tag(v___x_5644_) == 0 {
                    v_a_5645_ = lean_ctor_get(v___x_5644_, 0);
                    lean_inc(v_a_5645_);
                    lean_dec_ref_known(v___x_5644_, 1);
                    v___x_5646_ = (lean_unbox(v_a_5645_) as u8);
                    lean_dec(v_a_5645_);
                    if v___x_5646_ == 0 {
                        v_a_5620_ = v_candidates_5639_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5647_ = l_Lean_LocalDecl_hasValue(v_val_5628_, v___x_5634_);
                        if v___x_5647_ == 0 {
                            v___y_5630_ = v_candidates_5639_;
                            state = 4;
                            continue;
                        } else {
                            if v___x_5634_ == 0 {
                                v_a_5620_ = v_candidates_5639_;
                                state = 2;
                                continue;
                            } else {
                                v___y_5630_ = v_candidates_5639_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_candidates_5639_);
                    lean_del_object(v___x_5616_);
                    v_a_5648_ = lean_ctor_get(v___x_5644_, 0);
                    v_isSharedCheck_5655_ = (!lean_is_exclusive(v___x_5644_)) as u8;
                    if v_isSharedCheck_5655_ == 0 {
                        v___x_5650_ = v___x_5644_;
                        v_isShared_5651_ = v_isSharedCheck_5655_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5648_);
                        lean_dec(v___x_5644_);
                        v___x_5650_ = lean_box(0);
                        v_isShared_5651_ = v_isSharedCheck_5655_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5651_ == 0 {
                    v___x_5653_ = v___x_5650_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5654_, 0, v_a_5648_);
                    v___x_5653_ = v_reuseFailAlloc_5654_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5653_;
            }
            8 => {
                if v_isShared_5665_ == 0 {
                    v___x_5667_ = v___x_5664_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5668_, 0, v_a_5662_);
                    v___x_5667_ = v_reuseFailAlloc_5668_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5667_;
            }
            10 => {
                if v_isShared_5673_ == 0 {
                    v___x_5675_ = v___x_5672_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5676_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5676_, 0, v_a_5670_);
                    v___x_5675_ = v_reuseFailAlloc_5676_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___boxed(
    mut v_as_5680_: *mut LeanObject,
    mut v_sz_5681_: *mut LeanObject,
    mut v_i_5682_: *mut LeanObject,
    mut v_b_5683_: *mut LeanObject,
    mut v___y_5684_: *mut LeanObject,
    mut v___y_5685_: *mut LeanObject,
    mut v___y_5686_: *mut LeanObject,
    mut v___y_5687_: *mut LeanObject,
    mut v___y_5688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5689_: usize = 0;
    let mut v_i_boxed_5690_: usize = 0;
    let mut v_res_5691_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5689_ = lean_unbox_usize(v_sz_5681_);
    lean_dec(v_sz_5681_);
    v_i_boxed_5690_ = lean_unbox_usize(v_i_5682_);
    lean_dec(v_i_5682_);
    v_res_5691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_as_5680_, v_sz_boxed_5689_, v_i_boxed_5690_, v_b_5683_, v___y_5684_, v___y_5685_, v___y_5686_, v___y_5687_);
    lean_dec(v___y_5687_);
    lean_dec_ref(v___y_5686_);
    lean_dec(v___y_5685_);
    lean_dec_ref(v___y_5684_);
    lean_dec_ref(v_as_5680_);
    return v_res_5691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(
    mut v_as_5692_: *mut LeanObject,
    mut v_sz_5693_: usize,
    mut v_i_5694_: usize,
    mut v_b_5695_: *mut LeanObject,
    mut v___y_5696_: *mut LeanObject,
    mut v___y_5697_: *mut LeanObject,
    mut v___y_5698_: *mut LeanObject,
    mut v___y_5699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5701_: u8 = 0;
    let mut v___x_5702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5706_: u8 = 0;
    let mut v___x_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5712_: usize = 0;
    let mut v___x_5713_: usize = 0;
    let mut v_reuseFailAlloc_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: u8 = 0;
    let mut v___f_5724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_candidates_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: u8 = 0;
    let mut v___x_5736_: u8 = 0;
    let mut v_a_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5740_: u8 = 0;
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5744_: u8 = 0;
    let mut v___x_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5754_: u8 = 0;
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5758_: u8 = 0;
    let mut v_a_5759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5762_: u8 = 0;
    let mut v___x_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_isSharedCheck_5767_: u8 = 0;
    let mut v_unused_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5701_ = lean_usize_dec_lt(v_i_5694_, v_sz_5693_);
                if v___x_5701_ == 0 {
                    v___x_5702_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5702_, 0, v_b_5695_);
                    return v___x_5702_;
                } else {
                    v_snd_5703_ = lean_ctor_get(v_b_5695_, 1);
                    v_isSharedCheck_5767_ = (!lean_is_exclusive(v_b_5695_)) as u8;
                    if v_isSharedCheck_5767_ == 0 {
                        v_unused_5768_ = lean_ctor_get(v_b_5695_, 0);
                        lean_dec(v_unused_5768_);
                        v___x_5705_ = v_b_5695_;
                        v_isShared_5706_ = v_isSharedCheck_5767_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5703_);
                        lean_dec(v_b_5695_);
                        v___x_5705_ = lean_box(0);
                        v_isShared_5706_ = v_isSharedCheck_5767_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5707_ = lean_box(0);
                v_a_5716_ = lean_array_uget_borrowed(v_as_5692_, v_i_5694_);
                if lean_obj_tag(v_a_5716_) == 0 {
                    v_a_5709_ = v_snd_5703_;
                    state = 2;
                    continue;
                } else {
                    v_val_5717_ = lean_ctor_get(v_a_5716_, 0);
                    v___x_5723_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5717_);
                    if v___x_5723_ == 0 {
                        v___f_5724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5726_ = l_Lean_LocalDecl_type(v_val_5717_);
                        lean_inc_ref(v___x_5726_);
                        v___x_5745_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5725_, v___f_5724_, v___x_5723_, v___x_5726_, v_snd_5703_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
                        if lean_obj_tag(v___x_5745_) == 0 {
                            v_a_5746_ = lean_ctor_get(v___x_5745_, 0);
                            lean_inc(v_a_5746_);
                            lean_dec_ref_known(v___x_5745_, 1);
                            v___x_5747_ = l_Lean_LocalDecl_value_x3f(v_val_5717_, v___x_5723_);
                            if lean_obj_tag(v___x_5747_) == 0 {
                                v_candidates_5728_ = v_a_5746_;
                                v___y_5729_ = v___y_5696_;
                                v___y_5730_ = v___y_5697_;
                                v___y_5731_ = v___y_5698_;
                                v___y_5732_ = v___y_5699_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5748_ = lean_ctor_get(v___x_5747_, 0);
                                lean_inc(v_val_5748_);
                                lean_dec_ref_known(v___x_5747_, 1);
                                v___x_5749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5725_, v___f_5724_, v___x_5723_, v_val_5748_, v_a_5746_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
                                if lean_obj_tag(v___x_5749_) == 0 {
                                    v_a_5750_ = lean_ctor_get(v___x_5749_, 0);
                                    lean_inc(v_a_5750_);
                                    lean_dec_ref_known(v___x_5749_, 1);
                                    v_candidates_5728_ = v_a_5750_;
                                    v___y_5729_ = v___y_5696_;
                                    v___y_5730_ = v___y_5697_;
                                    v___y_5731_ = v___y_5698_;
                                    v___y_5732_ = v___y_5699_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec_ref(v___x_5726_);
                                    lean_del_object(v___x_5705_);
                                    v_a_5751_ = lean_ctor_get(v___x_5749_, 0);
                                    v_isSharedCheck_5758_ = (!lean_is_exclusive(v___x_5749_)) as u8;
                                    if v_isSharedCheck_5758_ == 0 {
                                        v___x_5753_ = v___x_5749_;
                                        v_isShared_5754_ = v_isSharedCheck_5758_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5751_);
                                        lean_dec(v___x_5749_);
                                        v___x_5753_ = lean_box(0);
                                        v_isShared_5754_ = v_isSharedCheck_5758_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_5726_);
                            lean_del_object(v___x_5705_);
                            v_a_5759_ = lean_ctor_get(v___x_5745_, 0);
                            v_isSharedCheck_5766_ = (!lean_is_exclusive(v___x_5745_)) as u8;
                            if v_isSharedCheck_5766_ == 0 {
                                v___x_5761_ = v___x_5745_;
                                v_isShared_5762_ = v_isSharedCheck_5766_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_5759_);
                                lean_dec(v___x_5745_);
                                v___x_5761_ = lean_box(0);
                                v_isShared_5762_ = v_isSharedCheck_5766_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_a_5709_ = v_snd_5703_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5706_ == 0 {
                    lean_ctor_set(v___x_5705_, 1, v_a_5709_);
                    lean_ctor_set(v___x_5705_, 0, v___x_5707_);
                    v___x_5711_ = v___x_5705_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5715_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5707_);
                    lean_ctor_set(v_reuseFailAlloc_5715_, 1, v_a_5709_);
                    v___x_5711_ = v_reuseFailAlloc_5715_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5712_ = 1usize;
                v___x_5713_ = lean_usize_add(v_i_5694_, v___x_5712_);
                v_i_5694_ = v___x_5713_;
                v_b_5695_ = v___x_5711_;
                state = 0;
                continue;
            }
            4 => {
                v___x_5720_ = l_Lean_LocalDecl_fvarId(v_val_5717_);
                v___x_5721_ = lean_box(0);
                v___x_5722_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_5719_, v___x_5720_, v___x_5721_);
                v_a_5709_ = v___x_5722_;
                state = 2;
                continue;
            }
            5 => {
                v___x_5733_ = l_Lean_Meta_isProp(
                    v___x_5726_,
                    v___y_5729_,
                    v___y_5730_,
                    v___y_5731_,
                    v___y_5732_,
                );
                if lean_obj_tag(v___x_5733_) == 0 {
                    v_a_5734_ = lean_ctor_get(v___x_5733_, 0);
                    lean_inc(v_a_5734_);
                    lean_dec_ref_known(v___x_5733_, 1);
                    v___x_5735_ = (lean_unbox(v_a_5734_) as u8);
                    lean_dec(v_a_5734_);
                    if v___x_5735_ == 0 {
                        v_a_5709_ = v_candidates_5728_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5736_ = l_Lean_LocalDecl_hasValue(v_val_5717_, v___x_5723_);
                        if v___x_5736_ == 0 {
                            v___y_5719_ = v_candidates_5728_;
                            state = 4;
                            continue;
                        } else {
                            if v___x_5723_ == 0 {
                                v_a_5709_ = v_candidates_5728_;
                                state = 2;
                                continue;
                            } else {
                                v___y_5719_ = v_candidates_5728_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_candidates_5728_);
                    lean_del_object(v___x_5705_);
                    v_a_5737_ = lean_ctor_get(v___x_5733_, 0);
                    v_isSharedCheck_5744_ = (!lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5744_ == 0 {
                        v___x_5739_ = v___x_5733_;
                        v_isShared_5740_ = v_isSharedCheck_5744_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5737_);
                        lean_dec(v___x_5733_);
                        v___x_5739_ = lean_box(0);
                        v_isShared_5740_ = v_isSharedCheck_5744_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5740_ == 0 {
                    v___x_5742_ = v___x_5739_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5743_, 0, v_a_5737_);
                    v___x_5742_ = v_reuseFailAlloc_5743_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5742_;
            }
            8 => {
                if v_isShared_5754_ == 0 {
                    v___x_5756_ = v___x_5753_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5757_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5757_, 0, v_a_5751_);
                    v___x_5756_ = v_reuseFailAlloc_5757_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5756_;
            }
            10 => {
                if v_isShared_5762_ == 0 {
                    v___x_5764_ = v___x_5761_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5759_);
                    v___x_5764_ = v_reuseFailAlloc_5765_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18___boxed(
    mut v_as_5769_: *mut LeanObject,
    mut v_sz_5770_: *mut LeanObject,
    mut v_i_5771_: *mut LeanObject,
    mut v_b_5772_: *mut LeanObject,
    mut v___y_5773_: *mut LeanObject,
    mut v___y_5774_: *mut LeanObject,
    mut v___y_5775_: *mut LeanObject,
    mut v___y_5776_: *mut LeanObject,
    mut v___y_5777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5778_: usize = 0;
    let mut v_i_boxed_5779_: usize = 0;
    let mut v_res_5780_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5778_ = lean_unbox_usize(v_sz_5770_);
    lean_dec(v_sz_5770_);
    v_i_boxed_5779_ = lean_unbox_usize(v_i_5771_);
    lean_dec(v_i_5771_);
    v_res_5780_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_5769_, v_sz_boxed_5778_, v_i_boxed_5779_, v_b_5772_, v___y_5773_, v___y_5774_, v___y_5775_, v___y_5776_);
    lean_dec(v___y_5776_);
    lean_dec_ref(v___y_5775_);
    lean_dec(v___y_5774_);
    lean_dec_ref(v___y_5773_);
    lean_dec_ref(v_as_5769_);
    return v_res_5780_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(
    mut v_as_5781_: *mut LeanObject,
    mut v_sz_5782_: usize,
    mut v_i_5783_: usize,
    mut v_b_5784_: *mut LeanObject,
    mut v___y_5785_: *mut LeanObject,
    mut v___y_5786_: *mut LeanObject,
    mut v___y_5787_: *mut LeanObject,
    mut v___y_5788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5790_: u8 = 0;
    let mut v___x_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5795_: u8 = 0;
    let mut v___x_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5801_: usize = 0;
    let mut v___x_5802_: usize = 0;
    let mut v___x_5803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: u8 = 0;
    let mut v___f_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_candidates_5817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: u8 = 0;
    let mut v___x_5825_: u8 = 0;
    let mut v_a_5826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5829_: u8 = 0;
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5833_: u8 = 0;
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5847_: u8 = 0;
    let mut v_a_5848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5851_: u8 = 0;
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5855_: u8 = 0;
    let mut v_isSharedCheck_5856_: u8 = 0;
    let mut v_unused_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5790_ = lean_usize_dec_lt(v_i_5783_, v_sz_5782_);
                if v___x_5790_ == 0 {
                    v___x_5791_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5791_, 0, v_b_5784_);
                    return v___x_5791_;
                } else {
                    v_snd_5792_ = lean_ctor_get(v_b_5784_, 1);
                    v_isSharedCheck_5856_ = (!lean_is_exclusive(v_b_5784_)) as u8;
                    if v_isSharedCheck_5856_ == 0 {
                        v_unused_5857_ = lean_ctor_get(v_b_5784_, 0);
                        lean_dec(v_unused_5857_);
                        v___x_5794_ = v_b_5784_;
                        v_isShared_5795_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5792_);
                        lean_dec(v_b_5784_);
                        v___x_5794_ = lean_box(0);
                        v_isShared_5795_ = v_isSharedCheck_5856_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5796_ = lean_box(0);
                v_a_5805_ = lean_array_uget_borrowed(v_as_5781_, v_i_5783_);
                if lean_obj_tag(v_a_5805_) == 0 {
                    v_a_5798_ = v_snd_5792_;
                    state = 2;
                    continue;
                } else {
                    v_val_5806_ = lean_ctor_get(v_a_5805_, 0);
                    v___x_5812_ = l_Lean_LocalDecl_isImplementationDetail(v_val_5806_);
                    if v___x_5812_ == 0 {
                        v___f_5813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__0;
                        v___f_5814_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8_spec__14___closed__1;
                        v___x_5815_ = l_Lean_LocalDecl_type(v_val_5806_);
                        lean_inc_ref(v___x_5815_);
                        v___x_5834_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5814_, v___f_5813_, v___x_5812_, v___x_5815_, v_snd_5792_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
                        if lean_obj_tag(v___x_5834_) == 0 {
                            v_a_5835_ = lean_ctor_get(v___x_5834_, 0);
                            lean_inc(v_a_5835_);
                            lean_dec_ref_known(v___x_5834_, 1);
                            v___x_5836_ = l_Lean_LocalDecl_value_x3f(v_val_5806_, v___x_5812_);
                            if lean_obj_tag(v___x_5836_) == 0 {
                                v_candidates_5817_ = v_a_5835_;
                                v___y_5818_ = v___y_5785_;
                                v___y_5819_ = v___y_5786_;
                                v___y_5820_ = v___y_5787_;
                                v___y_5821_ = v___y_5788_;
                                state = 5;
                                continue;
                            } else {
                                v_val_5837_ = lean_ctor_get(v___x_5836_, 0);
                                lean_inc(v_val_5837_);
                                lean_dec_ref_known(v___x_5836_, 1);
                                v___x_5838_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2(v___f_5814_, v___f_5813_, v___x_5812_, v_val_5837_, v_a_5835_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
                                if lean_obj_tag(v___x_5838_) == 0 {
                                    v_a_5839_ = lean_ctor_get(v___x_5838_, 0);
                                    lean_inc(v_a_5839_);
                                    lean_dec_ref_known(v___x_5838_, 1);
                                    v_candidates_5817_ = v_a_5839_;
                                    v___y_5818_ = v___y_5785_;
                                    v___y_5819_ = v___y_5786_;
                                    v___y_5820_ = v___y_5787_;
                                    v___y_5821_ = v___y_5788_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec_ref(v___x_5815_);
                                    lean_del_object(v___x_5794_);
                                    v_a_5840_ = lean_ctor_get(v___x_5838_, 0);
                                    v_isSharedCheck_5847_ = (!lean_is_exclusive(v___x_5838_)) as u8;
                                    if v_isSharedCheck_5847_ == 0 {
                                        v___x_5842_ = v___x_5838_;
                                        v_isShared_5843_ = v_isSharedCheck_5847_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5840_);
                                        lean_dec(v___x_5838_);
                                        v___x_5842_ = lean_box(0);
                                        v_isShared_5843_ = v_isSharedCheck_5847_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_5815_);
                            lean_del_object(v___x_5794_);
                            v_a_5848_ = lean_ctor_get(v___x_5834_, 0);
                            v_isSharedCheck_5855_ = (!lean_is_exclusive(v___x_5834_)) as u8;
                            if v_isSharedCheck_5855_ == 0 {
                                v___x_5850_ = v___x_5834_;
                                v_isShared_5851_ = v_isSharedCheck_5855_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_5848_);
                                lean_dec(v___x_5834_);
                                v___x_5850_ = lean_box(0);
                                v_isShared_5851_ = v_isSharedCheck_5855_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        v_a_5798_ = v_snd_5792_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5795_ == 0 {
                    lean_ctor_set(v___x_5794_, 1, v_a_5798_);
                    lean_ctor_set(v___x_5794_, 0, v___x_5796_);
                    v___x_5800_ = v___x_5794_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5804_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5804_, 0, v___x_5796_);
                    lean_ctor_set(v_reuseFailAlloc_5804_, 1, v_a_5798_);
                    v___x_5800_ = v_reuseFailAlloc_5804_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5801_ = 1usize;
                v___x_5802_ = lean_usize_add(v_i_5783_, v___x_5801_);
                v___x_5803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12_spec__18(v_as_5781_, v_sz_5782_, v___x_5802_, v___x_5800_, v___y_5785_, v___y_5786_, v___y_5787_, v___y_5788_);
                return v___x_5803_;
            }
            4 => {
                v___x_5809_ = l_Lean_LocalDecl_fvarId(v_val_5806_);
                v___x_5810_ = lean_box(0);
                v___x_5811_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v___y_5808_, v___x_5809_, v___x_5810_);
                v_a_5798_ = v___x_5811_;
                state = 2;
                continue;
            }
            5 => {
                v___x_5822_ = l_Lean_Meta_isProp(
                    v___x_5815_,
                    v___y_5818_,
                    v___y_5819_,
                    v___y_5820_,
                    v___y_5821_,
                );
                if lean_obj_tag(v___x_5822_) == 0 {
                    v_a_5823_ = lean_ctor_get(v___x_5822_, 0);
                    lean_inc(v_a_5823_);
                    lean_dec_ref_known(v___x_5822_, 1);
                    v___x_5824_ = (lean_unbox(v_a_5823_) as u8);
                    lean_dec(v_a_5823_);
                    if v___x_5824_ == 0 {
                        v_a_5798_ = v_candidates_5817_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5825_ = l_Lean_LocalDecl_hasValue(v_val_5806_, v___x_5812_);
                        if v___x_5825_ == 0 {
                            v___y_5808_ = v_candidates_5817_;
                            state = 4;
                            continue;
                        } else {
                            if v___x_5812_ == 0 {
                                v_a_5798_ = v_candidates_5817_;
                                state = 2;
                                continue;
                            } else {
                                v___y_5808_ = v_candidates_5817_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_candidates_5817_);
                    lean_del_object(v___x_5794_);
                    v_a_5826_ = lean_ctor_get(v___x_5822_, 0);
                    v_isSharedCheck_5833_ = (!lean_is_exclusive(v___x_5822_)) as u8;
                    if v_isSharedCheck_5833_ == 0 {
                        v___x_5828_ = v___x_5822_;
                        v_isShared_5829_ = v_isSharedCheck_5833_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5826_);
                        lean_dec(v___x_5822_);
                        v___x_5828_ = lean_box(0);
                        v_isShared_5829_ = v_isSharedCheck_5833_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_5829_ == 0 {
                    v___x_5831_ = v___x_5828_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5832_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5832_, 0, v_a_5826_);
                    v___x_5831_ = v_reuseFailAlloc_5832_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5831_;
            }
            8 => {
                if v_isShared_5843_ == 0 {
                    v___x_5845_ = v___x_5842_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5846_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5846_, 0, v_a_5840_);
                    v___x_5845_ = v_reuseFailAlloc_5846_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5845_;
            }
            10 => {
                if v_isShared_5851_ == 0 {
                    v___x_5853_ = v___x_5850_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5854_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5854_, 0, v_a_5848_);
                    v___x_5853_ = v_reuseFailAlloc_5854_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5853_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12___boxed(
    mut v_as_5858_: *mut LeanObject,
    mut v_sz_5859_: *mut LeanObject,
    mut v_i_5860_: *mut LeanObject,
    mut v_b_5861_: *mut LeanObject,
    mut v___y_5862_: *mut LeanObject,
    mut v___y_5863_: *mut LeanObject,
    mut v___y_5864_: *mut LeanObject,
    mut v___y_5865_: *mut LeanObject,
    mut v___y_5866_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5867_: usize = 0;
    let mut v_i_boxed_5868_: usize = 0;
    let mut v_res_5869_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5867_ = lean_unbox_usize(v_sz_5859_);
    lean_dec(v_sz_5859_);
    v_i_boxed_5868_ = lean_unbox_usize(v_i_5860_);
    lean_dec(v_i_5860_);
    v_res_5869_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_as_5858_, v_sz_boxed_5867_, v_i_boxed_5868_, v_b_5861_, v___y_5862_, v___y_5863_, v___y_5864_, v___y_5865_);
    lean_dec(v___y_5865_);
    lean_dec_ref(v___y_5864_);
    lean_dec(v___y_5863_);
    lean_dec_ref(v___y_5862_);
    lean_dec_ref(v_as_5858_);
    return v_res_5869_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(
    mut v_init_5870_: *mut LeanObject,
    mut v_n_5871_: *mut LeanObject,
    mut v_b_5872_: *mut LeanObject,
    mut v___y_5873_: *mut LeanObject,
    mut v___y_5874_: *mut LeanObject,
    mut v___y_5875_: *mut LeanObject,
    mut v___y_5876_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5881_: usize = 0;
    let mut v___x_5882_: usize = 0;
    let mut v___x_5883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v_fst_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5898_: u8 = 0;
    let mut v_a_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5902_: u8 = 0;
    let mut v___x_5904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5906_: u8 = 0;
    let mut v_vs_5907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5910_: usize = 0;
    let mut v___x_5911_: usize = 0;
    let mut v___x_5912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5916_: u8 = 0;
    let mut v_fst_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5927_: u8 = 0;
    let mut v_a_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5931_: u8 = 0;
    let mut v___x_5933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5935_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5871_) == 0 {
                    v_cs_5878_ = lean_ctor_get(v_n_5871_, 0);
                    v___x_5879_ = lean_box(0);
                    v___x_5880_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5880_, 0, v___x_5879_);
                    lean_ctor_set(v___x_5880_, 1, v_b_5872_);
                    v_sz_5881_ = lean_array_size(v_cs_5878_);
                    v___x_5882_ = 0usize;
                    v___x_5883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_5870_, v_cs_5878_, v_sz_5881_, v___x_5882_, v___x_5880_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
                    if lean_obj_tag(v___x_5883_) == 0 {
                        v_a_5884_ = lean_ctor_get(v___x_5883_, 0);
                        v_isSharedCheck_5898_ = (!lean_is_exclusive(v___x_5883_)) as u8;
                        if v_isSharedCheck_5898_ == 0 {
                            v___x_5886_ = v___x_5883_;
                            v_isShared_5887_ = v_isSharedCheck_5898_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5884_);
                            lean_dec(v___x_5883_);
                            v___x_5886_ = lean_box(0);
                            v_isShared_5887_ = v_isSharedCheck_5898_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5899_ = lean_ctor_get(v___x_5883_, 0);
                        v_isSharedCheck_5906_ = (!lean_is_exclusive(v___x_5883_)) as u8;
                        if v_isSharedCheck_5906_ == 0 {
                            v___x_5901_ = v___x_5883_;
                            v_isShared_5902_ = v_isSharedCheck_5906_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5899_);
                            lean_dec(v___x_5883_);
                            v___x_5901_ = lean_box(0);
                            v_isShared_5902_ = v_isSharedCheck_5906_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5907_ = lean_ctor_get(v_n_5871_, 0);
                    v___x_5908_ = lean_box(0);
                    v___x_5909_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5909_, 0, v___x_5908_);
                    lean_ctor_set(v___x_5909_, 1, v_b_5872_);
                    v_sz_5910_ = lean_array_size(v_vs_5907_);
                    v___x_5911_ = 0usize;
                    v___x_5912_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__12(v_vs_5907_, v_sz_5910_, v___x_5911_, v___x_5909_, v___y_5873_, v___y_5874_, v___y_5875_, v___y_5876_);
                    if lean_obj_tag(v___x_5912_) == 0 {
                        v_a_5913_ = lean_ctor_get(v___x_5912_, 0);
                        v_isSharedCheck_5927_ = (!lean_is_exclusive(v___x_5912_)) as u8;
                        if v_isSharedCheck_5927_ == 0 {
                            v___x_5915_ = v___x_5912_;
                            v_isShared_5916_ = v_isSharedCheck_5927_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5913_);
                            lean_dec(v___x_5912_);
                            v___x_5915_ = lean_box(0);
                            v_isShared_5916_ = v_isSharedCheck_5927_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5928_ = lean_ctor_get(v___x_5912_, 0);
                        v_isSharedCheck_5935_ = (!lean_is_exclusive(v___x_5912_)) as u8;
                        if v_isSharedCheck_5935_ == 0 {
                            v___x_5930_ = v___x_5912_;
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5928_);
                            lean_dec(v___x_5912_);
                            v___x_5930_ = lean_box(0);
                            v_isShared_5931_ = v_isSharedCheck_5935_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5888_ = lean_ctor_get(v_a_5884_, 0);
                if lean_obj_tag(v_fst_5888_) == 0 {
                    v_snd_5889_ = lean_ctor_get(v_a_5884_, 1);
                    lean_inc(v_snd_5889_);
                    lean_dec(v_a_5884_);
                    v___x_5890_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5890_, 0, v_snd_5889_);
                    if v_isShared_5887_ == 0 {
                        lean_ctor_set(v___x_5886_, 0, v___x_5890_);
                        v___x_5892_ = v___x_5886_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5893_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5893_, 0, v___x_5890_);
                        v___x_5892_ = v_reuseFailAlloc_5893_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5888_);
                    lean_dec(v_a_5884_);
                    v_val_5894_ = lean_ctor_get(v_fst_5888_, 0);
                    lean_inc(v_val_5894_);
                    lean_dec_ref_known(v_fst_5888_, 1);
                    if v_isShared_5887_ == 0 {
                        lean_ctor_set(v___x_5886_, 0, v_val_5894_);
                        v___x_5896_ = v___x_5886_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5897_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5897_, 0, v_val_5894_);
                        v___x_5896_ = v_reuseFailAlloc_5897_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5892_;
            }
            3 => {
                return v___x_5896_;
            }
            4 => {
                if v_isShared_5902_ == 0 {
                    v___x_5904_ = v___x_5901_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5905_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5905_, 0, v_a_5899_);
                    v___x_5904_ = v_reuseFailAlloc_5905_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5904_;
            }
            6 => {
                v_fst_5917_ = lean_ctor_get(v_a_5913_, 0);
                if lean_obj_tag(v_fst_5917_) == 0 {
                    v_snd_5918_ = lean_ctor_get(v_a_5913_, 1);
                    lean_inc(v_snd_5918_);
                    lean_dec(v_a_5913_);
                    v___x_5919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5919_, 0, v_snd_5918_);
                    if v_isShared_5916_ == 0 {
                        lean_ctor_set(v___x_5915_, 0, v___x_5919_);
                        v___x_5921_ = v___x_5915_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5922_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5922_, 0, v___x_5919_);
                        v___x_5921_ = v_reuseFailAlloc_5922_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5917_);
                    lean_dec(v_a_5913_);
                    v_val_5923_ = lean_ctor_get(v_fst_5917_, 0);
                    lean_inc(v_val_5923_);
                    lean_dec_ref_known(v_fst_5917_, 1);
                    if v_isShared_5916_ == 0 {
                        lean_ctor_set(v___x_5915_, 0, v_val_5923_);
                        v___x_5925_ = v___x_5915_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5926_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5926_, 0, v_val_5923_);
                        v___x_5925_ = v_reuseFailAlloc_5926_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5921_;
            }
            8 => {
                return v___x_5925_;
            }
            9 => {
                if v_isShared_5931_ == 0 {
                    v___x_5933_ = v___x_5930_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5934_, 0, v_a_5928_);
                    v___x_5933_ = v_reuseFailAlloc_5934_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5933_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(
    mut v_init_5936_: *mut LeanObject,
    mut v_as_5937_: *mut LeanObject,
    mut v_sz_5938_: usize,
    mut v_i_5939_: usize,
    mut v_b_5940_: *mut LeanObject,
    mut v___y_5941_: *mut LeanObject,
    mut v___y_5942_: *mut LeanObject,
    mut v___y_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5946_: u8 = 0;
    let mut v___x_5947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5951_: u8 = 0;
    let mut v_a_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5957_: u8 = 0;
    let mut v___x_5958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: usize = 0;
    let mut v___x_5970_: usize = 0;
    let mut v_reuseFailAlloc_5972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5973_: u8 = 0;
    let mut v_a_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5977_: u8 = 0;
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5981_: u8 = 0;
    let mut v_isSharedCheck_5982_: u8 = 0;
    let mut v_unused_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5946_ = lean_usize_dec_lt(v_i_5939_, v_sz_5938_);
                if v___x_5946_ == 0 {
                    v___x_5947_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5947_, 0, v_b_5940_);
                    return v___x_5947_;
                } else {
                    v_snd_5948_ = lean_ctor_get(v_b_5940_, 1);
                    v_isSharedCheck_5982_ = (!lean_is_exclusive(v_b_5940_)) as u8;
                    if v_isSharedCheck_5982_ == 0 {
                        v_unused_5983_ = lean_ctor_get(v_b_5940_, 0);
                        lean_dec(v_unused_5983_);
                        v___x_5950_ = v_b_5940_;
                        v_isShared_5951_ = v_isSharedCheck_5982_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5948_);
                        lean_dec(v_b_5940_);
                        v___x_5950_ = lean_box(0);
                        v_isShared_5951_ = v_isSharedCheck_5982_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5952_ = lean_array_uget_borrowed(v_as_5937_, v_i_5939_);
                lean_inc(v_snd_5948_);
                v___x_5953_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_5936_, v_a_5952_, v_snd_5948_, v___y_5941_, v___y_5942_, v___y_5943_, v___y_5944_);
                if lean_obj_tag(v___x_5953_) == 0 {
                    v_a_5954_ = lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_5973_ = (!lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_5973_ == 0 {
                        v___x_5956_ = v___x_5953_;
                        v_isShared_5957_ = v_isSharedCheck_5973_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5954_);
                        lean_dec(v___x_5953_);
                        v___x_5956_ = lean_box(0);
                        v_isShared_5957_ = v_isSharedCheck_5973_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5950_);
                    lean_dec(v_snd_5948_);
                    v_a_5974_ = lean_ctor_get(v___x_5953_, 0);
                    v_isSharedCheck_5981_ = (!lean_is_exclusive(v___x_5953_)) as u8;
                    if v_isSharedCheck_5981_ == 0 {
                        v___x_5976_ = v___x_5953_;
                        v_isShared_5977_ = v_isSharedCheck_5981_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5974_);
                        lean_dec(v___x_5953_);
                        v___x_5976_ = lean_box(0);
                        v_isShared_5977_ = v_isSharedCheck_5981_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5954_) == 0 {
                    v___x_5958_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5958_, 0, v_a_5954_);
                    if v_isShared_5951_ == 0 {
                        lean_ctor_set(v___x_5950_, 0, v___x_5958_);
                        v___x_5960_ = v___x_5950_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5964_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5964_, 0, v___x_5958_);
                        lean_ctor_set(v_reuseFailAlloc_5964_, 1, v_snd_5948_);
                        v___x_5960_ = v_reuseFailAlloc_5964_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5956_);
                    lean_dec(v_snd_5948_);
                    v_a_5965_ = lean_ctor_get(v_a_5954_, 0);
                    lean_inc(v_a_5965_);
                    lean_dec_ref_known(v_a_5954_, 1);
                    v___x_5966_ = lean_box(0);
                    if v_isShared_5951_ == 0 {
                        lean_ctor_set(v___x_5950_, 1, v_a_5965_);
                        lean_ctor_set(v___x_5950_, 0, v___x_5966_);
                        v___x_5968_ = v___x_5950_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5972_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5972_, 0, v___x_5966_);
                        lean_ctor_set(v_reuseFailAlloc_5972_, 1, v_a_5965_);
                        v___x_5968_ = v_reuseFailAlloc_5972_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5957_ == 0 {
                    lean_ctor_set(v___x_5956_, 0, v___x_5960_);
                    v___x_5962_ = v___x_5956_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5963_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5963_, 0, v___x_5960_);
                    v___x_5962_ = v_reuseFailAlloc_5963_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5962_;
            }
            5 => {
                v___x_5969_ = 1usize;
                v___x_5970_ = lean_usize_add(v_i_5939_, v___x_5969_);
                v_i_5939_ = v___x_5970_;
                v_b_5940_ = v___x_5968_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5977_ == 0 {
                    v___x_5979_ = v___x_5976_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5980_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5980_, 0, v_a_5974_);
                    v___x_5979_ = v_reuseFailAlloc_5980_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11___boxed(
    mut v_init_5984_: *mut LeanObject,
    mut v_as_5985_: *mut LeanObject,
    mut v_sz_5986_: *mut LeanObject,
    mut v_i_5987_: *mut LeanObject,
    mut v_b_5988_: *mut LeanObject,
    mut v___y_5989_: *mut LeanObject,
    mut v___y_5990_: *mut LeanObject,
    mut v___y_5991_: *mut LeanObject,
    mut v___y_5992_: *mut LeanObject,
    mut v___y_5993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5994_: usize = 0;
    let mut v_i_boxed_5995_: usize = 0;
    let mut v_res_5996_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5994_ = lean_unbox_usize(v_sz_5986_);
    lean_dec(v_sz_5986_);
    v_i_boxed_5995_ = lean_unbox_usize(v_i_5987_);
    lean_dec(v_i_5987_);
    v_res_5996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7_spec__11(v_init_5984_, v_as_5985_, v_sz_boxed_5994_, v_i_boxed_5995_, v_b_5988_, v___y_5989_, v___y_5990_, v___y_5991_, v___y_5992_);
    lean_dec(v___y_5992_);
    lean_dec_ref(v___y_5991_);
    lean_dec(v___y_5990_);
    lean_dec_ref(v___y_5989_);
    lean_dec_ref(v_as_5985_);
    lean_dec_ref(v_init_5984_);
    return v_res_5996_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7___boxed(
    mut v_init_5997_: *mut LeanObject,
    mut v_n_5998_: *mut LeanObject,
    mut v_b_5999_: *mut LeanObject,
    mut v___y_6000_: *mut LeanObject,
    mut v___y_6001_: *mut LeanObject,
    mut v___y_6002_: *mut LeanObject,
    mut v___y_6003_: *mut LeanObject,
    mut v___y_6004_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6005_: *mut LeanObject = core::ptr::null_mut();
    v_res_6005_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_5997_, v_n_5998_, v_b_5999_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_);
    lean_dec(v___y_6003_);
    lean_dec_ref(v___y_6002_);
    lean_dec(v___y_6001_);
    lean_dec_ref(v___y_6000_);
    lean_dec_ref(v_n_5998_);
    lean_dec_ref(v_init_5997_);
    return v_res_6005_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(
    mut v_t_6006_: *mut LeanObject,
    mut v_init_6007_: *mut LeanObject,
    mut v___y_6008_: *mut LeanObject,
    mut v___y_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
    mut v___y_6011_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6019_: u8 = 0;
    let mut v_a_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6027_: usize = 0;
    let mut v___x_6028_: usize = 0;
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6033_: u8 = 0;
    let mut v_fst_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6043_: u8 = 0;
    let mut v_a_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6047_: u8 = 0;
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6051_: u8 = 0;
    let mut v_isSharedCheck_6052_: u8 = 0;
    let mut v_a_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6056_: u8 = 0;
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6060_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6013_ = lean_ctor_get(v_t_6006_, 0);
                v_tail_6014_ = lean_ctor_get(v_t_6006_, 1);
                lean_inc_ref(v_init_6007_);
                v___x_6015_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__7(v_init_6007_, v_root_6013_, v_init_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
                lean_dec_ref(v_init_6007_);
                if lean_obj_tag(v___x_6015_) == 0 {
                    v_a_6016_ = lean_ctor_get(v___x_6015_, 0);
                    v_isSharedCheck_6052_ = (!lean_is_exclusive(v___x_6015_)) as u8;
                    if v_isSharedCheck_6052_ == 0 {
                        v___x_6018_ = v___x_6015_;
                        v_isShared_6019_ = v_isSharedCheck_6052_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6016_);
                        lean_dec(v___x_6015_);
                        v___x_6018_ = lean_box(0);
                        v_isShared_6019_ = v_isSharedCheck_6052_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6053_ = lean_ctor_get(v___x_6015_, 0);
                    v_isSharedCheck_6060_ = (!lean_is_exclusive(v___x_6015_)) as u8;
                    if v_isSharedCheck_6060_ == 0 {
                        v___x_6055_ = v___x_6015_;
                        v_isShared_6056_ = v_isSharedCheck_6060_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6053_);
                        lean_dec(v___x_6015_);
                        v___x_6055_ = lean_box(0);
                        v_isShared_6056_ = v_isSharedCheck_6060_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6016_) == 0 {
                    v_a_6020_ = lean_ctor_get(v_a_6016_, 0);
                    lean_inc(v_a_6020_);
                    lean_dec_ref_known(v_a_6016_, 1);
                    if v_isShared_6019_ == 0 {
                        lean_ctor_set(v___x_6018_, 0, v_a_6020_);
                        v___x_6022_ = v___x_6018_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6023_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_a_6020_);
                        v___x_6022_ = v_reuseFailAlloc_6023_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6018_);
                    v_a_6024_ = lean_ctor_get(v_a_6016_, 0);
                    lean_inc(v_a_6024_);
                    lean_dec_ref_known(v_a_6016_, 1);
                    v___x_6025_ = lean_box(0);
                    v___x_6026_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6026_, 0, v___x_6025_);
                    lean_ctor_set(v___x_6026_, 1, v_a_6024_);
                    v_sz_6027_ = lean_array_size(v_tail_6014_);
                    v___x_6028_ = 0usize;
                    v___x_6029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8(v_tail_6014_, v_sz_6027_, v___x_6028_, v___x_6026_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_);
                    if lean_obj_tag(v___x_6029_) == 0 {
                        v_a_6030_ = lean_ctor_get(v___x_6029_, 0);
                        v_isSharedCheck_6043_ = (!lean_is_exclusive(v___x_6029_)) as u8;
                        if v_isSharedCheck_6043_ == 0 {
                            v___x_6032_ = v___x_6029_;
                            v_isShared_6033_ = v_isSharedCheck_6043_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6030_);
                            lean_dec(v___x_6029_);
                            v___x_6032_ = lean_box(0);
                            v_isShared_6033_ = v_isSharedCheck_6043_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6044_ = lean_ctor_get(v___x_6029_, 0);
                        v_isSharedCheck_6051_ = (!lean_is_exclusive(v___x_6029_)) as u8;
                        if v_isSharedCheck_6051_ == 0 {
                            v___x_6046_ = v___x_6029_;
                            v_isShared_6047_ = v_isSharedCheck_6051_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6044_);
                            lean_dec(v___x_6029_);
                            v___x_6046_ = lean_box(0);
                            v_isShared_6047_ = v_isSharedCheck_6051_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6022_;
            }
            3 => {
                v_fst_6034_ = lean_ctor_get(v_a_6030_, 0);
                if lean_obj_tag(v_fst_6034_) == 0 {
                    v_snd_6035_ = lean_ctor_get(v_a_6030_, 1);
                    lean_inc(v_snd_6035_);
                    lean_dec(v_a_6030_);
                    if v_isShared_6033_ == 0 {
                        lean_ctor_set(v___x_6032_, 0, v_snd_6035_);
                        v___x_6037_ = v___x_6032_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6038_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_snd_6035_);
                        v___x_6037_ = v_reuseFailAlloc_6038_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6034_);
                    lean_dec(v_a_6030_);
                    v_val_6039_ = lean_ctor_get(v_fst_6034_, 0);
                    lean_inc(v_val_6039_);
                    lean_dec_ref_known(v_fst_6034_, 1);
                    if v_isShared_6033_ == 0 {
                        lean_ctor_set(v___x_6032_, 0, v_val_6039_);
                        v___x_6041_ = v___x_6032_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6042_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6042_, 0, v_val_6039_);
                        v___x_6041_ = v_reuseFailAlloc_6042_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6037_;
            }
            5 => {
                return v___x_6041_;
            }
            6 => {
                if v_isShared_6047_ == 0 {
                    v___x_6049_ = v___x_6046_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6050_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6050_, 0, v_a_6044_);
                    v___x_6049_ = v_reuseFailAlloc_6050_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6049_;
            }
            8 => {
                if v_isShared_6056_ == 0 {
                    v___x_6058_ = v___x_6055_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6059_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6059_, 0, v_a_6053_);
                    v___x_6058_ = v_reuseFailAlloc_6059_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3___boxed(
    mut v_t_6061_: *mut LeanObject,
    mut v_init_6062_: *mut LeanObject,
    mut v___y_6063_: *mut LeanObject,
    mut v___y_6064_: *mut LeanObject,
    mut v___y_6065_: *mut LeanObject,
    mut v___y_6066_: *mut LeanObject,
    mut v___y_6067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6068_: *mut LeanObject = core::ptr::null_mut();
    v_res_6068_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(
        v_t_6061_,
        v_init_6062_,
        v___y_6063_,
        v___y_6064_,
        v___y_6065_,
        v___y_6066_,
    );
    lean_dec(v___y_6066_);
    lean_dec_ref(v___y_6065_);
    lean_dec(v___y_6064_);
    lean_dec_ref(v___y_6063_);
    lean_dec_ref(v_t_6061_);
    return v_res_6068_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(
    mut v_m_6069_: *mut LeanObject,
    mut v_a_6070_: *mut LeanObject,
) -> u8 {
    let mut v_buckets_6071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6073_: u64 = 0;
    let mut v___x_6074_: u64 = 0;
    let mut v___x_6075_: u64 = 0;
    let mut v_fold_6076_: u64 = 0;
    let mut v___x_6077_: u64 = 0;
    let mut v___x_6078_: u64 = 0;
    let mut v___x_6079_: u64 = 0;
    let mut v___x_6080_: usize = 0;
    let mut v___x_6081_: usize = 0;
    let mut v___x_6082_: usize = 0;
    let mut v___x_6083_: usize = 0;
    let mut v___x_6084_: usize = 0;
    let mut v___x_6085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: u8 = 0;
    v_buckets_6071_ = lean_ctor_get(v_m_6069_, 1);
    v___x_6072_ = lean_array_get_size(v_buckets_6071_);
    v___x_6073_ = l_Lean_instHashableFVarId_hash(v_a_6070_);
    v___x_6074_ = 32u64;
    v___x_6075_ = lean_uint64_shift_right(v___x_6073_, v___x_6074_);
    v_fold_6076_ = lean_uint64_xor(v___x_6073_, v___x_6075_);
    v___x_6077_ = 16u64;
    v___x_6078_ = lean_uint64_shift_right(v_fold_6076_, v___x_6077_);
    v___x_6079_ = lean_uint64_xor(v_fold_6076_, v___x_6078_);
    v___x_6080_ = lean_uint64_to_usize(v___x_6079_);
    v___x_6081_ = lean_usize_of_nat(v___x_6072_);
    v___x_6082_ = 1usize;
    v___x_6083_ = lean_usize_sub(v___x_6081_, v___x_6082_);
    v___x_6084_ = lean_usize_land(v___x_6080_, v___x_6083_);
    v___x_6085_ = lean_array_uget_borrowed(v_buckets_6071_, v___x_6084_);
    v___x_6086_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_6070_, v___x_6085_);
    return v___x_6086_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg___boxed(
    mut v_m_6087_: *mut LeanObject,
    mut v_a_6088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6089_: u8 = 0;
    let mut v_r_6090_: *mut LeanObject = core::ptr::null_mut();
    v_res_6089_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_6087_, v_a_6088_);
    lean_dec(v_a_6088_);
    lean_dec_ref(v_m_6087_);
    v_r_6090_ = lean_box((v_res_6089_) as usize);
    return v_r_6090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(
    mut v_a_6091_: *mut LeanObject,
    mut v_as_6092_: *mut LeanObject,
    mut v_sz_6093_: usize,
    mut v_i_6094_: usize,
    mut v_b_6095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6097_: u8 = 0;
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6102_: u8 = 0;
    let mut v___x_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: usize = 0;
    let mut v___x_6109_: usize = 0;
    let mut v_reuseFailAlloc_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6115_: u8 = 0;
    let mut v___x_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6117_: u8 = 0;
    let mut v_unused_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6097_ = lean_usize_dec_lt(v_i_6094_, v_sz_6093_);
                if v___x_6097_ == 0 {
                    v___x_6098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6098_, 0, v_b_6095_);
                    return v___x_6098_;
                } else {
                    v_snd_6099_ = lean_ctor_get(v_b_6095_, 1);
                    v_isSharedCheck_6117_ = (!lean_is_exclusive(v_b_6095_)) as u8;
                    if v_isSharedCheck_6117_ == 0 {
                        v_unused_6118_ = lean_ctor_get(v_b_6095_, 0);
                        lean_dec(v_unused_6118_);
                        v___x_6101_ = v_b_6095_;
                        v_isShared_6102_ = v_isSharedCheck_6117_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6099_);
                        lean_dec(v_b_6095_);
                        v___x_6101_ = lean_box(0);
                        v_isShared_6102_ = v_isSharedCheck_6117_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6103_ = lean_box(0);
                v_a_6112_ = lean_array_uget_borrowed(v_as_6092_, v_i_6094_);
                if lean_obj_tag(v_a_6112_) == 0 {
                    v_a_6105_ = v_snd_6099_;
                    state = 2;
                    continue;
                } else {
                    v_val_6113_ = lean_ctor_get(v_a_6112_, 0);
                    v___x_6114_ = l_Lean_LocalDecl_fvarId(v_val_6113_);
                    v___x_6115_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6091_, v___x_6114_);
                    if v___x_6115_ == 0 {
                        lean_dec(v___x_6114_);
                        v_a_6105_ = v_snd_6099_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6116_ = lean_array_push(v_snd_6099_, v___x_6114_);
                        v_a_6105_ = v___x_6116_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6102_ == 0 {
                    lean_ctor_set(v___x_6101_, 1, v_a_6105_);
                    lean_ctor_set(v___x_6101_, 0, v___x_6103_);
                    v___x_6107_ = v___x_6101_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6111_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6111_, 0, v___x_6103_);
                    lean_ctor_set(v_reuseFailAlloc_6111_, 1, v_a_6105_);
                    v___x_6107_ = v_reuseFailAlloc_6111_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6108_ = 1usize;
                v___x_6109_ = lean_usize_add(v_i_6094_, v___x_6108_);
                v_i_6094_ = v___x_6109_;
                v_b_6095_ = v___x_6107_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg___boxed(
    mut v_a_6119_: *mut LeanObject,
    mut v_as_6120_: *mut LeanObject,
    mut v_sz_6121_: *mut LeanObject,
    mut v_i_6122_: *mut LeanObject,
    mut v_b_6123_: *mut LeanObject,
    mut v___y_6124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6125_: usize = 0;
    let mut v_i_boxed_6126_: usize = 0;
    let mut v_res_6127_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6125_ = lean_unbox_usize(v_sz_6121_);
    lean_dec(v_sz_6121_);
    v_i_boxed_6126_ = lean_unbox_usize(v_i_6122_);
    lean_dec(v_i_6122_);
    v_res_6127_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_6119_, v_as_6120_, v_sz_boxed_6125_, v_i_boxed_6126_, v_b_6123_);
    lean_dec_ref(v_as_6120_);
    lean_dec_ref(v_a_6119_);
    return v_res_6127_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(
    mut v_a_6128_: *mut LeanObject,
    mut v_as_6129_: *mut LeanObject,
    mut v_sz_6130_: usize,
    mut v_i_6131_: usize,
    mut v_b_6132_: *mut LeanObject,
    mut v___y_6133_: *mut LeanObject,
    mut v___y_6134_: *mut LeanObject,
    mut v___y_6135_: *mut LeanObject,
    mut v___y_6136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6138_: u8 = 0;
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6143_: u8 = 0;
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6149_: usize = 0;
    let mut v___x_6150_: usize = 0;
    let mut v___x_6151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: u8 = 0;
    let mut v___x_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6158_: u8 = 0;
    let mut v_unused_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6138_ = lean_usize_dec_lt(v_i_6131_, v_sz_6130_);
                if v___x_6138_ == 0 {
                    v___x_6139_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6139_, 0, v_b_6132_);
                    return v___x_6139_;
                } else {
                    v_snd_6140_ = lean_ctor_get(v_b_6132_, 1);
                    v_isSharedCheck_6158_ = (!lean_is_exclusive(v_b_6132_)) as u8;
                    if v_isSharedCheck_6158_ == 0 {
                        v_unused_6159_ = lean_ctor_get(v_b_6132_, 0);
                        lean_dec(v_unused_6159_);
                        v___x_6142_ = v_b_6132_;
                        v_isShared_6143_ = v_isSharedCheck_6158_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6140_);
                        lean_dec(v_b_6132_);
                        v___x_6142_ = lean_box(0);
                        v_isShared_6143_ = v_isSharedCheck_6158_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6144_ = lean_box(0);
                v_a_6153_ = lean_array_uget_borrowed(v_as_6129_, v_i_6131_);
                if lean_obj_tag(v_a_6153_) == 0 {
                    v_a_6146_ = v_snd_6140_;
                    state = 2;
                    continue;
                } else {
                    v_val_6154_ = lean_ctor_get(v_a_6153_, 0);
                    v___x_6155_ = l_Lean_LocalDecl_fvarId(v_val_6154_);
                    v___x_6156_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6128_, v___x_6155_);
                    if v___x_6156_ == 0 {
                        lean_dec(v___x_6155_);
                        v_a_6146_ = v_snd_6140_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6157_ = lean_array_push(v_snd_6140_, v___x_6155_);
                        v_a_6146_ = v___x_6157_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6143_ == 0 {
                    lean_ctor_set(v___x_6142_, 1, v_a_6146_);
                    lean_ctor_set(v___x_6142_, 0, v___x_6144_);
                    v___x_6148_ = v___x_6142_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6152_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6152_, 0, v___x_6144_);
                    lean_ctor_set(v_reuseFailAlloc_6152_, 1, v_a_6146_);
                    v___x_6148_ = v_reuseFailAlloc_6152_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6149_ = 1usize;
                v___x_6150_ = lean_usize_add(v_i_6131_, v___x_6149_);
                v___x_6151_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_6128_, v_as_6129_, v_sz_6130_, v___x_6150_, v___x_6148_);
                return v___x_6151_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19___boxed(
    mut v_a_6160_: *mut LeanObject,
    mut v_as_6161_: *mut LeanObject,
    mut v_sz_6162_: *mut LeanObject,
    mut v_i_6163_: *mut LeanObject,
    mut v_b_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
    mut v___y_6168_: *mut LeanObject,
    mut v___y_6169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6170_: usize = 0;
    let mut v_i_boxed_6171_: usize = 0;
    let mut v_res_6172_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6170_ = lean_unbox_usize(v_sz_6162_);
    lean_dec(v_sz_6162_);
    v_i_boxed_6171_ = lean_unbox_usize(v_i_6163_);
    lean_dec(v_i_6163_);
    v_res_6172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_6160_, v_as_6161_, v_sz_boxed_6170_, v_i_boxed_6171_, v_b_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_);
    lean_dec(v___y_6168_);
    lean_dec_ref(v___y_6167_);
    lean_dec(v___y_6166_);
    lean_dec_ref(v___y_6165_);
    lean_dec_ref(v_as_6161_);
    lean_dec_ref(v_a_6160_);
    return v_res_6172_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(
    mut v_init_6173_: *mut LeanObject,
    mut v_a_6174_: *mut LeanObject,
    mut v_n_6175_: *mut LeanObject,
    mut v_b_6176_: *mut LeanObject,
    mut v___y_6177_: *mut LeanObject,
    mut v___y_6178_: *mut LeanObject,
    mut v___y_6179_: *mut LeanObject,
    mut v___y_6180_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6185_: usize = 0;
    let mut v___x_6186_: usize = 0;
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6191_: u8 = 0;
    let mut v_fst_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6202_: u8 = 0;
    let mut v_a_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6206_: u8 = 0;
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_vs_6211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6214_: usize = 0;
    let mut v___x_6215_: usize = 0;
    let mut v___x_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6220_: u8 = 0;
    let mut v_fst_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_a_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_6175_) == 0 {
                    v_cs_6182_ = lean_ctor_get(v_n_6175_, 0);
                    v___x_6183_ = lean_box(0);
                    v___x_6184_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6184_, 0, v___x_6183_);
                    lean_ctor_set(v___x_6184_, 1, v_b_6176_);
                    v_sz_6185_ = lean_array_size(v_cs_6182_);
                    v___x_6186_ = 0usize;
                    v___x_6187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_6173_, v_a_6174_, v_cs_6182_, v_sz_6185_, v___x_6186_, v___x_6184_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
                    if lean_obj_tag(v___x_6187_) == 0 {
                        v_a_6188_ = lean_ctor_get(v___x_6187_, 0);
                        v_isSharedCheck_6202_ = (!lean_is_exclusive(v___x_6187_)) as u8;
                        if v_isSharedCheck_6202_ == 0 {
                            v___x_6190_ = v___x_6187_;
                            v_isShared_6191_ = v_isSharedCheck_6202_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6188_);
                            lean_dec(v___x_6187_);
                            v___x_6190_ = lean_box(0);
                            v_isShared_6191_ = v_isSharedCheck_6202_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6203_ = lean_ctor_get(v___x_6187_, 0);
                        v_isSharedCheck_6210_ = (!lean_is_exclusive(v___x_6187_)) as u8;
                        if v_isSharedCheck_6210_ == 0 {
                            v___x_6205_ = v___x_6187_;
                            v_isShared_6206_ = v_isSharedCheck_6210_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6203_);
                            lean_dec(v___x_6187_);
                            v___x_6205_ = lean_box(0);
                            v_isShared_6206_ = v_isSharedCheck_6210_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6211_ = lean_ctor_get(v_n_6175_, 0);
                    v___x_6212_ = lean_box(0);
                    v___x_6213_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6213_, 0, v___x_6212_);
                    lean_ctor_set(v___x_6213_, 1, v_b_6176_);
                    v_sz_6214_ = lean_array_size(v_vs_6211_);
                    v___x_6215_ = 0usize;
                    v___x_6216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19(v_a_6174_, v_vs_6211_, v_sz_6214_, v___x_6215_, v___x_6213_, v___y_6177_, v___y_6178_, v___y_6179_, v___y_6180_);
                    if lean_obj_tag(v___x_6216_) == 0 {
                        v_a_6217_ = lean_ctor_get(v___x_6216_, 0);
                        v_isSharedCheck_6231_ = (!lean_is_exclusive(v___x_6216_)) as u8;
                        if v_isSharedCheck_6231_ == 0 {
                            v___x_6219_ = v___x_6216_;
                            v_isShared_6220_ = v_isSharedCheck_6231_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6217_);
                            lean_dec(v___x_6216_);
                            v___x_6219_ = lean_box(0);
                            v_isShared_6220_ = v_isSharedCheck_6231_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6232_ = lean_ctor_get(v___x_6216_, 0);
                        v_isSharedCheck_6239_ = (!lean_is_exclusive(v___x_6216_)) as u8;
                        if v_isSharedCheck_6239_ == 0 {
                            v___x_6234_ = v___x_6216_;
                            v_isShared_6235_ = v_isSharedCheck_6239_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6232_);
                            lean_dec(v___x_6216_);
                            v___x_6234_ = lean_box(0);
                            v_isShared_6235_ = v_isSharedCheck_6239_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6192_ = lean_ctor_get(v_a_6188_, 0);
                if lean_obj_tag(v_fst_6192_) == 0 {
                    v_snd_6193_ = lean_ctor_get(v_a_6188_, 1);
                    lean_inc(v_snd_6193_);
                    lean_dec(v_a_6188_);
                    v___x_6194_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6194_, 0, v_snd_6193_);
                    if v_isShared_6191_ == 0 {
                        lean_ctor_set(v___x_6190_, 0, v___x_6194_);
                        v___x_6196_ = v___x_6190_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6197_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6197_, 0, v___x_6194_);
                        v___x_6196_ = v_reuseFailAlloc_6197_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6192_);
                    lean_dec(v_a_6188_);
                    v_val_6198_ = lean_ctor_get(v_fst_6192_, 0);
                    lean_inc(v_val_6198_);
                    lean_dec_ref_known(v_fst_6192_, 1);
                    if v_isShared_6191_ == 0 {
                        lean_ctor_set(v___x_6190_, 0, v_val_6198_);
                        v___x_6200_ = v___x_6190_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6201_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6201_, 0, v_val_6198_);
                        v___x_6200_ = v_reuseFailAlloc_6201_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6196_;
            }
            3 => {
                return v___x_6200_;
            }
            4 => {
                if v_isShared_6206_ == 0 {
                    v___x_6208_ = v___x_6205_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
                    v___x_6208_ = v_reuseFailAlloc_6209_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6208_;
            }
            6 => {
                v_fst_6221_ = lean_ctor_get(v_a_6217_, 0);
                if lean_obj_tag(v_fst_6221_) == 0 {
                    v_snd_6222_ = lean_ctor_get(v_a_6217_, 1);
                    lean_inc(v_snd_6222_);
                    lean_dec(v_a_6217_);
                    v___x_6223_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6223_, 0, v_snd_6222_);
                    if v_isShared_6220_ == 0 {
                        lean_ctor_set(v___x_6219_, 0, v___x_6223_);
                        v___x_6225_ = v___x_6219_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6226_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6226_, 0, v___x_6223_);
                        v___x_6225_ = v_reuseFailAlloc_6226_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6221_);
                    lean_dec(v_a_6217_);
                    v_val_6227_ = lean_ctor_get(v_fst_6221_, 0);
                    lean_inc(v_val_6227_);
                    lean_dec_ref_known(v_fst_6221_, 1);
                    if v_isShared_6220_ == 0 {
                        lean_ctor_set(v___x_6219_, 0, v_val_6227_);
                        v___x_6229_ = v___x_6219_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6230_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_val_6227_);
                        v___x_6229_ = v_reuseFailAlloc_6230_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6225_;
            }
            8 => {
                return v___x_6229_;
            }
            9 => {
                if v_isShared_6235_ == 0 {
                    v___x_6237_ = v___x_6234_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6238_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
                    v___x_6237_ = v_reuseFailAlloc_6238_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(
    mut v_init_6240_: *mut LeanObject,
    mut v_a_6241_: *mut LeanObject,
    mut v_as_6242_: *mut LeanObject,
    mut v_sz_6243_: usize,
    mut v_i_6244_: usize,
    mut v_b_6245_: *mut LeanObject,
    mut v___y_6246_: *mut LeanObject,
    mut v___y_6247_: *mut LeanObject,
    mut v___y_6248_: *mut LeanObject,
    mut v___y_6249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6251_: u8 = 0;
    let mut v___x_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6256_: u8 = 0;
    let mut v_a_6257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6262_: u8 = 0;
    let mut v___x_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6274_: usize = 0;
    let mut v___x_6275_: usize = 0;
    let mut v_reuseFailAlloc_6277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6278_: u8 = 0;
    let mut v_a_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6282_: u8 = 0;
    let mut v___x_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6286_: u8 = 0;
    let mut v_isSharedCheck_6287_: u8 = 0;
    let mut v_unused_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6251_ = lean_usize_dec_lt(v_i_6244_, v_sz_6243_);
                if v___x_6251_ == 0 {
                    v___x_6252_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6252_, 0, v_b_6245_);
                    return v___x_6252_;
                } else {
                    v_snd_6253_ = lean_ctor_get(v_b_6245_, 1);
                    v_isSharedCheck_6287_ = (!lean_is_exclusive(v_b_6245_)) as u8;
                    if v_isSharedCheck_6287_ == 0 {
                        v_unused_6288_ = lean_ctor_get(v_b_6245_, 0);
                        lean_dec(v_unused_6288_);
                        v___x_6255_ = v_b_6245_;
                        v_isShared_6256_ = v_isSharedCheck_6287_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6253_);
                        lean_dec(v_b_6245_);
                        v___x_6255_ = lean_box(0);
                        v_isShared_6256_ = v_isSharedCheck_6287_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6257_ = lean_array_uget_borrowed(v_as_6242_, v_i_6244_);
                lean_inc(v_snd_6253_);
                v___x_6258_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_6240_, v_a_6241_, v_a_6257_, v_snd_6253_, v___y_6246_, v___y_6247_, v___y_6248_, v___y_6249_);
                if lean_obj_tag(v___x_6258_) == 0 {
                    v_a_6259_ = lean_ctor_get(v___x_6258_, 0);
                    v_isSharedCheck_6278_ = (!lean_is_exclusive(v___x_6258_)) as u8;
                    if v_isSharedCheck_6278_ == 0 {
                        v___x_6261_ = v___x_6258_;
                        v_isShared_6262_ = v_isSharedCheck_6278_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6259_);
                        lean_dec(v___x_6258_);
                        v___x_6261_ = lean_box(0);
                        v_isShared_6262_ = v_isSharedCheck_6278_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6255_);
                    lean_dec(v_snd_6253_);
                    v_a_6279_ = lean_ctor_get(v___x_6258_, 0);
                    v_isSharedCheck_6286_ = (!lean_is_exclusive(v___x_6258_)) as u8;
                    if v_isSharedCheck_6286_ == 0 {
                        v___x_6281_ = v___x_6258_;
                        v_isShared_6282_ = v_isSharedCheck_6286_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6279_);
                        lean_dec(v___x_6258_);
                        v___x_6281_ = lean_box(0);
                        v_isShared_6282_ = v_isSharedCheck_6286_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6259_) == 0 {
                    v___x_6263_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6263_, 0, v_a_6259_);
                    if v_isShared_6256_ == 0 {
                        lean_ctor_set(v___x_6255_, 0, v___x_6263_);
                        v___x_6265_ = v___x_6255_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6269_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6269_, 0, v___x_6263_);
                        lean_ctor_set(v_reuseFailAlloc_6269_, 1, v_snd_6253_);
                        v___x_6265_ = v_reuseFailAlloc_6269_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6261_);
                    lean_dec(v_snd_6253_);
                    v_a_6270_ = lean_ctor_get(v_a_6259_, 0);
                    lean_inc(v_a_6270_);
                    lean_dec_ref_known(v_a_6259_, 1);
                    v___x_6271_ = lean_box(0);
                    if v_isShared_6256_ == 0 {
                        lean_ctor_set(v___x_6255_, 1, v_a_6270_);
                        lean_ctor_set(v___x_6255_, 0, v___x_6271_);
                        v___x_6273_ = v___x_6255_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6277_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6277_, 0, v___x_6271_);
                        lean_ctor_set(v_reuseFailAlloc_6277_, 1, v_a_6270_);
                        v___x_6273_ = v_reuseFailAlloc_6277_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6262_ == 0 {
                    lean_ctor_set(v___x_6261_, 0, v___x_6265_);
                    v___x_6267_ = v___x_6261_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6268_, 0, v___x_6265_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6267_;
            }
            5 => {
                v___x_6274_ = 1usize;
                v___x_6275_ = lean_usize_add(v_i_6244_, v___x_6274_);
                v_i_6244_ = v___x_6275_;
                v_b_6245_ = v___x_6273_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6282_ == 0 {
                    v___x_6284_ = v___x_6281_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6285_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6285_, 0, v_a_6279_);
                    v___x_6284_ = v_reuseFailAlloc_6285_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18___boxed(
    mut v_init_6289_: *mut LeanObject,
    mut v_a_6290_: *mut LeanObject,
    mut v_as_6291_: *mut LeanObject,
    mut v_sz_6292_: *mut LeanObject,
    mut v_i_6293_: *mut LeanObject,
    mut v_b_6294_: *mut LeanObject,
    mut v___y_6295_: *mut LeanObject,
    mut v___y_6296_: *mut LeanObject,
    mut v___y_6297_: *mut LeanObject,
    mut v___y_6298_: *mut LeanObject,
    mut v___y_6299_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6300_: usize = 0;
    let mut v_i_boxed_6301_: usize = 0;
    let mut v_res_6302_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6300_ = lean_unbox_usize(v_sz_6292_);
    lean_dec(v_sz_6292_);
    v_i_boxed_6301_ = lean_unbox_usize(v_i_6293_);
    lean_dec(v_i_6293_);
    v_res_6302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__18(v_init_6289_, v_a_6290_, v_as_6291_, v_sz_boxed_6300_, v_i_boxed_6301_, v_b_6294_, v___y_6295_, v___y_6296_, v___y_6297_, v___y_6298_);
    lean_dec(v___y_6298_);
    lean_dec_ref(v___y_6297_);
    lean_dec(v___y_6296_);
    lean_dec_ref(v___y_6295_);
    lean_dec_ref(v_as_6291_);
    lean_dec_ref(v_a_6290_);
    lean_dec_ref(v_init_6289_);
    return v_res_6302_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11___boxed(
    mut v_init_6303_: *mut LeanObject,
    mut v_a_6304_: *mut LeanObject,
    mut v_n_6305_: *mut LeanObject,
    mut v_b_6306_: *mut LeanObject,
    mut v___y_6307_: *mut LeanObject,
    mut v___y_6308_: *mut LeanObject,
    mut v___y_6309_: *mut LeanObject,
    mut v___y_6310_: *mut LeanObject,
    mut v___y_6311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6312_: *mut LeanObject = core::ptr::null_mut();
    v_res_6312_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_6303_, v_a_6304_, v_n_6305_, v_b_6306_, v___y_6307_, v___y_6308_, v___y_6309_, v___y_6310_);
    lean_dec(v___y_6310_);
    lean_dec_ref(v___y_6309_);
    lean_dec(v___y_6308_);
    lean_dec_ref(v___y_6307_);
    lean_dec_ref(v_n_6305_);
    lean_dec_ref(v_a_6304_);
    lean_dec_ref(v_init_6303_);
    return v_res_6312_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(
    mut v_a_6313_: *mut LeanObject,
    mut v_as_6314_: *mut LeanObject,
    mut v_sz_6315_: usize,
    mut v_i_6316_: usize,
    mut v_b_6317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6319_: u8 = 0;
    let mut v___x_6320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6324_: u8 = 0;
    let mut v___x_6325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: usize = 0;
    let mut v___x_6331_: usize = 0;
    let mut v_reuseFailAlloc_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: u8 = 0;
    let mut v___x_6338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6339_: u8 = 0;
    let mut v_unused_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6319_ = lean_usize_dec_lt(v_i_6316_, v_sz_6315_);
                if v___x_6319_ == 0 {
                    v___x_6320_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6320_, 0, v_b_6317_);
                    return v___x_6320_;
                } else {
                    v_snd_6321_ = lean_ctor_get(v_b_6317_, 1);
                    v_isSharedCheck_6339_ = (!lean_is_exclusive(v_b_6317_)) as u8;
                    if v_isSharedCheck_6339_ == 0 {
                        v_unused_6340_ = lean_ctor_get(v_b_6317_, 0);
                        lean_dec(v_unused_6340_);
                        v___x_6323_ = v_b_6317_;
                        v_isShared_6324_ = v_isSharedCheck_6339_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6321_);
                        lean_dec(v_b_6317_);
                        v___x_6323_ = lean_box(0);
                        v_isShared_6324_ = v_isSharedCheck_6339_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6325_ = lean_box(0);
                v_a_6334_ = lean_array_uget_borrowed(v_as_6314_, v_i_6316_);
                if lean_obj_tag(v_a_6334_) == 0 {
                    v_a_6327_ = v_snd_6321_;
                    state = 2;
                    continue;
                } else {
                    v_val_6335_ = lean_ctor_get(v_a_6334_, 0);
                    v___x_6336_ = l_Lean_LocalDecl_fvarId(v_val_6335_);
                    v___x_6337_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6313_, v___x_6336_);
                    if v___x_6337_ == 0 {
                        lean_dec(v___x_6336_);
                        v_a_6327_ = v_snd_6321_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6338_ = lean_array_push(v_snd_6321_, v___x_6336_);
                        v_a_6327_ = v___x_6338_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6324_ == 0 {
                    lean_ctor_set(v___x_6323_, 1, v_a_6327_);
                    lean_ctor_set(v___x_6323_, 0, v___x_6325_);
                    v___x_6329_ = v___x_6323_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6333_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6333_, 0, v___x_6325_);
                    lean_ctor_set(v_reuseFailAlloc_6333_, 1, v_a_6327_);
                    v___x_6329_ = v_reuseFailAlloc_6333_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6330_ = 1usize;
                v___x_6331_ = lean_usize_add(v_i_6316_, v___x_6330_);
                v_i_6316_ = v___x_6331_;
                v_b_6317_ = v___x_6329_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg___boxed(
    mut v_a_6341_: *mut LeanObject,
    mut v_as_6342_: *mut LeanObject,
    mut v_sz_6343_: *mut LeanObject,
    mut v_i_6344_: *mut LeanObject,
    mut v_b_6345_: *mut LeanObject,
    mut v___y_6346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6347_: usize = 0;
    let mut v_i_boxed_6348_: usize = 0;
    let mut v_res_6349_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6347_ = lean_unbox_usize(v_sz_6343_);
    lean_dec(v_sz_6343_);
    v_i_boxed_6348_ = lean_unbox_usize(v_i_6344_);
    lean_dec(v_i_6344_);
    v_res_6349_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_6341_, v_as_6342_, v_sz_boxed_6347_, v_i_boxed_6348_, v_b_6345_);
    lean_dec_ref(v_as_6342_);
    lean_dec_ref(v_a_6341_);
    return v_res_6349_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(
    mut v_a_6350_: *mut LeanObject,
    mut v_as_6351_: *mut LeanObject,
    mut v_sz_6352_: usize,
    mut v_i_6353_: usize,
    mut v_b_6354_: *mut LeanObject,
    mut v___y_6355_: *mut LeanObject,
    mut v___y_6356_: *mut LeanObject,
    mut v___y_6357_: *mut LeanObject,
    mut v___y_6358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6360_: u8 = 0;
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: usize = 0;
    let mut v___x_6372_: usize = 0;
    let mut v___x_6373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6378_: u8 = 0;
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6380_: u8 = 0;
    let mut v_unused_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6360_ = lean_usize_dec_lt(v_i_6353_, v_sz_6352_);
                if v___x_6360_ == 0 {
                    v___x_6361_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6361_, 0, v_b_6354_);
                    return v___x_6361_;
                } else {
                    v_snd_6362_ = lean_ctor_get(v_b_6354_, 1);
                    v_isSharedCheck_6380_ = (!lean_is_exclusive(v_b_6354_)) as u8;
                    if v_isSharedCheck_6380_ == 0 {
                        v_unused_6381_ = lean_ctor_get(v_b_6354_, 0);
                        lean_dec(v_unused_6381_);
                        v___x_6364_ = v_b_6354_;
                        v_isShared_6365_ = v_isSharedCheck_6380_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6362_);
                        lean_dec(v_b_6354_);
                        v___x_6364_ = lean_box(0);
                        v_isShared_6365_ = v_isSharedCheck_6380_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6366_ = lean_box(0);
                v_a_6375_ = lean_array_uget_borrowed(v_as_6351_, v_i_6353_);
                if lean_obj_tag(v_a_6375_) == 0 {
                    v_a_6368_ = v_snd_6362_;
                    state = 2;
                    continue;
                } else {
                    v_val_6376_ = lean_ctor_get(v_a_6375_, 0);
                    v___x_6377_ = l_Lean_LocalDecl_fvarId(v_val_6376_);
                    v___x_6378_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_a_6350_, v___x_6377_);
                    if v___x_6378_ == 0 {
                        lean_dec(v___x_6377_);
                        v_a_6368_ = v_snd_6362_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6379_ = lean_array_push(v_snd_6362_, v___x_6377_);
                        v_a_6368_ = v___x_6379_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6365_ == 0 {
                    lean_ctor_set(v___x_6364_, 1, v_a_6368_);
                    lean_ctor_set(v___x_6364_, 0, v___x_6366_);
                    v___x_6370_ = v___x_6364_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6374_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6374_, 0, v___x_6366_);
                    lean_ctor_set(v_reuseFailAlloc_6374_, 1, v_a_6368_);
                    v___x_6370_ = v_reuseFailAlloc_6374_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6371_ = 1usize;
                v___x_6372_ = lean_usize_add(v_i_6353_, v___x_6371_);
                v___x_6373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_6350_, v_as_6351_, v_sz_6352_, v___x_6372_, v___x_6370_);
                return v___x_6373_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12___boxed(
    mut v_a_6382_: *mut LeanObject,
    mut v_as_6383_: *mut LeanObject,
    mut v_sz_6384_: *mut LeanObject,
    mut v_i_6385_: *mut LeanObject,
    mut v_b_6386_: *mut LeanObject,
    mut v___y_6387_: *mut LeanObject,
    mut v___y_6388_: *mut LeanObject,
    mut v___y_6389_: *mut LeanObject,
    mut v___y_6390_: *mut LeanObject,
    mut v___y_6391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6392_: usize = 0;
    let mut v_i_boxed_6393_: usize = 0;
    let mut v_res_6394_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6392_ = lean_unbox_usize(v_sz_6384_);
    lean_dec(v_sz_6384_);
    v_i_boxed_6393_ = lean_unbox_usize(v_i_6385_);
    lean_dec(v_i_6385_);
    v_res_6394_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_6382_, v_as_6383_, v_sz_boxed_6392_, v_i_boxed_6393_, v_b_6386_, v___y_6387_, v___y_6388_, v___y_6389_, v___y_6390_);
    lean_dec(v___y_6390_);
    lean_dec_ref(v___y_6389_);
    lean_dec(v___y_6388_);
    lean_dec_ref(v___y_6387_);
    lean_dec_ref(v_as_6383_);
    lean_dec_ref(v_a_6382_);
    return v_res_6394_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(
    mut v_a_6395_: *mut LeanObject,
    mut v_t_6396_: *mut LeanObject,
    mut v_init_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_6403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6409_: u8 = 0;
    let mut v_a_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6417_: usize = 0;
    let mut v___x_6418_: usize = 0;
    let mut v___x_6419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6423_: u8 = 0;
    let mut v_fst_6424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6433_: u8 = 0;
    let mut v_a_6434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6437_: u8 = 0;
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6441_: u8 = 0;
    let mut v_isSharedCheck_6442_: u8 = 0;
    let mut v_a_6443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6446_: u8 = 0;
    let mut v___x_6448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6403_ = lean_ctor_get(v_t_6396_, 0);
                v_tail_6404_ = lean_ctor_get(v_t_6396_, 1);
                lean_inc_ref(v_init_6397_);
                v___x_6405_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11(v_init_6397_, v_a_6395_, v_root_6403_, v_init_6397_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_);
                lean_dec_ref(v_init_6397_);
                if lean_obj_tag(v___x_6405_) == 0 {
                    v_a_6406_ = lean_ctor_get(v___x_6405_, 0);
                    v_isSharedCheck_6442_ = (!lean_is_exclusive(v___x_6405_)) as u8;
                    if v_isSharedCheck_6442_ == 0 {
                        v___x_6408_ = v___x_6405_;
                        v_isShared_6409_ = v_isSharedCheck_6442_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6406_);
                        lean_dec(v___x_6405_);
                        v___x_6408_ = lean_box(0);
                        v_isShared_6409_ = v_isSharedCheck_6442_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6443_ = lean_ctor_get(v___x_6405_, 0);
                    v_isSharedCheck_6450_ = (!lean_is_exclusive(v___x_6405_)) as u8;
                    if v_isSharedCheck_6450_ == 0 {
                        v___x_6445_ = v___x_6405_;
                        v_isShared_6446_ = v_isSharedCheck_6450_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6443_);
                        lean_dec(v___x_6405_);
                        v___x_6445_ = lean_box(0);
                        v_isShared_6446_ = v_isSharedCheck_6450_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6406_) == 0 {
                    v_a_6410_ = lean_ctor_get(v_a_6406_, 0);
                    lean_inc(v_a_6410_);
                    lean_dec_ref_known(v_a_6406_, 1);
                    if v_isShared_6409_ == 0 {
                        lean_ctor_set(v___x_6408_, 0, v_a_6410_);
                        v___x_6412_ = v___x_6408_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6413_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_a_6410_);
                        v___x_6412_ = v_reuseFailAlloc_6413_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6408_);
                    v_a_6414_ = lean_ctor_get(v_a_6406_, 0);
                    lean_inc(v_a_6414_);
                    lean_dec_ref_known(v_a_6406_, 1);
                    v___x_6415_ = lean_box(0);
                    v___x_6416_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6416_, 0, v___x_6415_);
                    lean_ctor_set(v___x_6416_, 1, v_a_6414_);
                    v_sz_6417_ = lean_array_size(v_tail_6404_);
                    v___x_6418_ = 0usize;
                    v___x_6419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12(v_a_6395_, v_tail_6404_, v_sz_6417_, v___x_6418_, v___x_6416_, v___y_6398_, v___y_6399_, v___y_6400_, v___y_6401_);
                    if lean_obj_tag(v___x_6419_) == 0 {
                        v_a_6420_ = lean_ctor_get(v___x_6419_, 0);
                        v_isSharedCheck_6433_ = (!lean_is_exclusive(v___x_6419_)) as u8;
                        if v_isSharedCheck_6433_ == 0 {
                            v___x_6422_ = v___x_6419_;
                            v_isShared_6423_ = v_isSharedCheck_6433_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6420_);
                            lean_dec(v___x_6419_);
                            v___x_6422_ = lean_box(0);
                            v_isShared_6423_ = v_isSharedCheck_6433_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6434_ = lean_ctor_get(v___x_6419_, 0);
                        v_isSharedCheck_6441_ = (!lean_is_exclusive(v___x_6419_)) as u8;
                        if v_isSharedCheck_6441_ == 0 {
                            v___x_6436_ = v___x_6419_;
                            v_isShared_6437_ = v_isSharedCheck_6441_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6434_);
                            lean_dec(v___x_6419_);
                            v___x_6436_ = lean_box(0);
                            v_isShared_6437_ = v_isSharedCheck_6441_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6412_;
            }
            3 => {
                v_fst_6424_ = lean_ctor_get(v_a_6420_, 0);
                if lean_obj_tag(v_fst_6424_) == 0 {
                    v_snd_6425_ = lean_ctor_get(v_a_6420_, 1);
                    lean_inc(v_snd_6425_);
                    lean_dec(v_a_6420_);
                    if v_isShared_6423_ == 0 {
                        lean_ctor_set(v___x_6422_, 0, v_snd_6425_);
                        v___x_6427_ = v___x_6422_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6428_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6428_, 0, v_snd_6425_);
                        v___x_6427_ = v_reuseFailAlloc_6428_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6424_);
                    lean_dec(v_a_6420_);
                    v_val_6429_ = lean_ctor_get(v_fst_6424_, 0);
                    lean_inc(v_val_6429_);
                    lean_dec_ref_known(v_fst_6424_, 1);
                    if v_isShared_6423_ == 0 {
                        lean_ctor_set(v___x_6422_, 0, v_val_6429_);
                        v___x_6431_ = v___x_6422_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6432_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6432_, 0, v_val_6429_);
                        v___x_6431_ = v_reuseFailAlloc_6432_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6427_;
            }
            5 => {
                return v___x_6431_;
            }
            6 => {
                if v_isShared_6437_ == 0 {
                    v___x_6439_ = v___x_6436_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6440_, 0, v_a_6434_);
                    v___x_6439_ = v_reuseFailAlloc_6440_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6439_;
            }
            8 => {
                if v_isShared_6446_ == 0 {
                    v___x_6448_ = v___x_6445_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6449_, 0, v_a_6443_);
                    v___x_6448_ = v_reuseFailAlloc_6449_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5___boxed(
    mut v_a_6451_: *mut LeanObject,
    mut v_t_6452_: *mut LeanObject,
    mut v_init_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
    mut v___y_6455_: *mut LeanObject,
    mut v___y_6456_: *mut LeanObject,
    mut v___y_6457_: *mut LeanObject,
    mut v___y_6458_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6459_: *mut LeanObject = core::ptr::null_mut();
    v_res_6459_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(
        v_a_6451_,
        v_t_6452_,
        v_init_6453_,
        v___y_6454_,
        v___y_6455_,
        v___y_6456_,
        v___y_6457_,
    );
    lean_dec(v___y_6457_);
    lean_dec_ref(v___y_6456_);
    lean_dec(v___y_6455_);
    lean_dec_ref(v___y_6454_);
    lean_dec_ref(v_t_6452_);
    lean_dec_ref(v_a_6451_);
    return v_res_6459_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__2(
    mut v_candidates_6462_: *mut LeanObject,
    mut v_mvarId_6463_: *mut LeanObject,
    mut v___f_6464_: *mut LeanObject,
    mut v___f_6465_: *mut LeanObject,
    mut v___y_6466_: *mut LeanObject,
    mut v___y_6467_: *mut LeanObject,
    mut v___y_6468_: *mut LeanObject,
    mut v___y_6469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6485_: u8 = 0;
    let mut v___x_6486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: u8 = 0;
    let mut v___x_6490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6496_: u8 = 0;
    let mut v_a_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6500_: u8 = 0;
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6504_: u8 = 0;
    let mut v___x_6505_: u8 = 0;
    let mut v___x_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6509_: u8 = 0;
    let mut v___x_6510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6516_: u8 = 0;
    let mut v___x_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6520_: u8 = 0;
    let mut v_a_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6524_: u8 = 0;
    let mut v___x_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_a_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6536_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lctx_6471_ = lean_ctor_get(v___y_6466_, 2);
                v_decls_6472_ = lean_ctor_get(v_lctx_6471_, 1);
                lean_inc_ref(v_decls_6472_);
                v___x_6473_ =
                    l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3(
                        v_decls_6472_,
                        v_candidates_6462_,
                        v___y_6466_,
                        v___y_6467_,
                        v___y_6468_,
                        v___y_6469_,
                    );
                if lean_obj_tag(v___x_6473_) == 0 {
                    v_a_6474_ = lean_ctor_get(v___x_6473_, 0);
                    lean_inc(v_a_6474_);
                    lean_dec_ref_known(v___x_6473_, 1);
                    v___x_6475_ = l_Lean_MVarId_getType(
                        v_mvarId_6463_,
                        v___y_6466_,
                        v___y_6467_,
                        v___y_6468_,
                        v___y_6469_,
                    );
                    if lean_obj_tag(v___x_6475_) == 0 {
                        v_a_6476_ = lean_ctor_get(v___x_6475_, 0);
                        lean_inc(v_a_6476_);
                        lean_dec_ref_known(v___x_6475_, 1);
                        v___x_6477_ = l_Lean_instantiateMVars___at___00Lean_MVarId_getType_x27_spec__0___redArg(v_a_6476_, v___y_6467_);
                        v_a_6478_ = lean_ctor_get(v___x_6477_, 0);
                        lean_inc(v_a_6478_);
                        lean_dec_ref(v___x_6477_);
                        v___x_6479_ = lean_st_mk_ref(v_a_6474_);
                        v___x_6505_ = l_Lean_Expr_hasFVar(v_a_6478_);
                        if v___x_6505_ == 0 {
                            lean_dec(v_a_6478_);
                            lean_dec_ref(v___f_6465_);
                            v___x_6506_ = lean_box(0);
                            lean_inc(v___y_6469_);
                            lean_inc_ref(v___y_6468_);
                            lean_inc(v___y_6467_);
                            lean_inc_ref(v___y_6466_);
                            lean_inc(v___x_6479_);
                            v___x_6507_ = lean_apply_7(
                                v___f_6464_,
                                v___x_6506_,
                                v___x_6479_,
                                v___y_6466_,
                                v___y_6467_,
                                v___y_6468_,
                                v___y_6469_,
                                lean_box(0),
                            );
                            v___y_6481_ = v___x_6507_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6508_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__3_spec__8___lam__2___closed__0;
                            v___x_6509_ = 0;
                            v___x_6510_ = l_Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1(v___x_6508_, v___f_6465_, v_a_6478_, v___x_6509_, v___x_6479_, v___y_6466_, v___y_6467_, v___y_6468_, v___y_6469_);
                            if lean_obj_tag(v___x_6510_) == 0 {
                                v_a_6511_ = lean_ctor_get(v___x_6510_, 0);
                                lean_inc(v_a_6511_);
                                lean_dec_ref_known(v___x_6510_, 1);
                                lean_inc(v___y_6469_);
                                lean_inc_ref(v___y_6468_);
                                lean_inc(v___y_6467_);
                                lean_inc_ref(v___y_6466_);
                                lean_inc(v___x_6479_);
                                v___x_6512_ = lean_apply_7(
                                    v___f_6464_,
                                    v_a_6511_,
                                    v___x_6479_,
                                    v___y_6466_,
                                    v___y_6467_,
                                    v___y_6468_,
                                    v___y_6469_,
                                    lean_box(0),
                                );
                                v___y_6481_ = v___x_6512_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_6479_);
                                lean_dec_ref(v_decls_6472_);
                                lean_dec(v___y_6469_);
                                lean_dec_ref(v___y_6468_);
                                lean_dec(v___y_6467_);
                                lean_dec_ref(v___y_6466_);
                                lean_dec_ref(v___f_6464_);
                                v_a_6513_ = lean_ctor_get(v___x_6510_, 0);
                                v_isSharedCheck_6520_ = (!lean_is_exclusive(v___x_6510_)) as u8;
                                if v_isSharedCheck_6520_ == 0 {
                                    v___x_6515_ = v___x_6510_;
                                    v_isShared_6516_ = v_isSharedCheck_6520_;
                                    state = 6;
                                    continue;
                                } else {
                                    lean_inc(v_a_6513_);
                                    lean_dec(v___x_6510_);
                                    v___x_6515_ = lean_box(0);
                                    v_isShared_6516_ = v_isSharedCheck_6520_;
                                    state = 6;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_6474_);
                        lean_dec_ref(v_decls_6472_);
                        lean_dec(v___y_6469_);
                        lean_dec_ref(v___y_6468_);
                        lean_dec(v___y_6467_);
                        lean_dec_ref(v___y_6466_);
                        lean_dec_ref(v___f_6465_);
                        lean_dec_ref(v___f_6464_);
                        v_a_6521_ = lean_ctor_get(v___x_6475_, 0);
                        v_isSharedCheck_6528_ = (!lean_is_exclusive(v___x_6475_)) as u8;
                        if v_isSharedCheck_6528_ == 0 {
                            v___x_6523_ = v___x_6475_;
                            v_isShared_6524_ = v_isSharedCheck_6528_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_6521_);
                            lean_dec(v___x_6475_);
                            v___x_6523_ = lean_box(0);
                            v_isShared_6524_ = v_isSharedCheck_6528_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_decls_6472_);
                    lean_dec(v___y_6469_);
                    lean_dec_ref(v___y_6468_);
                    lean_dec(v___y_6467_);
                    lean_dec_ref(v___y_6466_);
                    lean_dec_ref(v___f_6465_);
                    lean_dec_ref(v___f_6464_);
                    lean_dec(v_mvarId_6463_);
                    v_a_6529_ = lean_ctor_get(v___x_6473_, 0);
                    v_isSharedCheck_6536_ = (!lean_is_exclusive(v___x_6473_)) as u8;
                    if v_isSharedCheck_6536_ == 0 {
                        v___x_6531_ = v___x_6473_;
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_6529_);
                        lean_dec(v___x_6473_);
                        v___x_6531_ = lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6536_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_6481_) == 0 {
                    v_a_6482_ = lean_ctor_get(v___y_6481_, 0);
                    v_isSharedCheck_6496_ = (!lean_is_exclusive(v___y_6481_)) as u8;
                    if v_isSharedCheck_6496_ == 0 {
                        v___x_6484_ = v___y_6481_;
                        v_isShared_6485_ = v_isSharedCheck_6496_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6482_);
                        lean_dec(v___y_6481_);
                        v___x_6484_ = lean_box(0);
                        v_isShared_6485_ = v_isSharedCheck_6496_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6479_);
                    lean_dec_ref(v_decls_6472_);
                    lean_dec(v___y_6469_);
                    lean_dec_ref(v___y_6468_);
                    lean_dec(v___y_6467_);
                    lean_dec_ref(v___y_6466_);
                    v_a_6497_ = lean_ctor_get(v___y_6481_, 0);
                    v_isSharedCheck_6504_ = (!lean_is_exclusive(v___y_6481_)) as u8;
                    if v_isSharedCheck_6504_ == 0 {
                        v___x_6499_ = v___y_6481_;
                        v_isShared_6500_ = v_isSharedCheck_6504_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6497_);
                        lean_dec(v___y_6481_);
                        v___x_6499_ = lean_box(0);
                        v_isShared_6500_ = v_isSharedCheck_6504_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6486_ = lean_st_ref_get(v___x_6479_);
                lean_dec(v___x_6479_);
                lean_dec(v___x_6486_);
                v_size_6487_ = lean_ctor_get(v_a_6482_, 0);
                v___x_6488_ = lean_unsigned_to_nat(0);
                v___x_6489_ = lean_nat_dec_eq(v_size_6487_, v___x_6488_);
                if v___x_6489_ == 0 {
                    lean_del_object(v___x_6484_);
                    v___x_6490_ = l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0;
                    v___x_6491_ =
                        l_Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5(
                            v_a_6482_,
                            v_decls_6472_,
                            v___x_6490_,
                            v___y_6466_,
                            v___y_6467_,
                            v___y_6468_,
                            v___y_6469_,
                        );
                    lean_dec(v___y_6469_);
                    lean_dec_ref(v___y_6468_);
                    lean_dec(v___y_6467_);
                    lean_dec_ref(v___y_6466_);
                    lean_dec_ref(v_decls_6472_);
                    lean_dec(v_a_6482_);
                    return v___x_6491_;
                } else {
                    lean_dec(v_a_6482_);
                    lean_dec_ref(v_decls_6472_);
                    lean_dec(v___y_6469_);
                    lean_dec_ref(v___y_6468_);
                    lean_dec(v___y_6467_);
                    lean_dec_ref(v___y_6466_);
                    v___x_6492_ = l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0;
                    if v_isShared_6485_ == 0 {
                        lean_ctor_set(v___x_6484_, 0, v___x_6492_);
                        v___x_6494_ = v___x_6484_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6495_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6495_, 0, v___x_6492_);
                        v___x_6494_ = v_reuseFailAlloc_6495_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_6494_;
            }
            4 => {
                if v_isShared_6500_ == 0 {
                    v___x_6502_ = v___x_6499_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6503_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6503_, 0, v_a_6497_);
                    v___x_6502_ = v_reuseFailAlloc_6503_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6502_;
            }
            6 => {
                if v_isShared_6516_ == 0 {
                    v___x_6518_ = v___x_6515_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6519_, 0, v_a_6513_);
                    v___x_6518_ = v_reuseFailAlloc_6519_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6518_;
            }
            8 => {
                if v_isShared_6524_ == 0 {
                    v___x_6526_ = v___x_6523_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6521_);
                    v___x_6526_ = v_reuseFailAlloc_6527_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6526_;
            }
            10 => {
                if v_isShared_6532_ == 0 {
                    v___x_6534_ = v___x_6531_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6535_, 0, v_a_6529_);
                    v___x_6534_ = v_reuseFailAlloc_6535_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6534_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___lam__2___boxed(
    mut v_candidates_6537_: *mut LeanObject,
    mut v_mvarId_6538_: *mut LeanObject,
    mut v___f_6539_: *mut LeanObject,
    mut v___f_6540_: *mut LeanObject,
    mut v___y_6541_: *mut LeanObject,
    mut v___y_6542_: *mut LeanObject,
    mut v___y_6543_: *mut LeanObject,
    mut v___y_6544_: *mut LeanObject,
    mut v___y_6545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6546_: *mut LeanObject = core::ptr::null_mut();
    v_res_6546_ = l_Lean_MVarId_getNondepPropHyps___lam__2(
        v_candidates_6537_,
        v_mvarId_6538_,
        v___f_6539_,
        v___f_6540_,
        v___y_6541_,
        v___y_6542_,
        v___y_6543_,
        v___y_6544_,
    );
    return v_res_6546_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps(
    mut v_mvarId_6549_: *mut LeanObject,
    mut v_a_6550_: *mut LeanObject,
    mut v_a_6551_: *mut LeanObject,
    mut v_a_6552_: *mut LeanObject,
    mut v_a_6553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_candidates_6557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6559_: *mut LeanObject = core::ptr::null_mut();
    v___f_6555_ = l_Lean_MVarId_getNondepPropHyps___closed__0;
    v___f_6556_ = l_Lean_MVarId_getNondepPropHyps___closed__1;
    v_candidates_6557_ = l_Lean_instEmptyCollectionFVarIdHashSet;
    lean_inc(v_mvarId_6549_);
    v___f_6558_ = lean_alloc_closure(
        l_Lean_MVarId_getNondepPropHyps___lam__2___boxed as *mut core::ffi::c_void,
        9,
        4,
    );
    lean_closure_set(v___f_6558_, 0, v_candidates_6557_);
    lean_closure_set(v___f_6558_, 1, v_mvarId_6549_);
    lean_closure_set(v___f_6558_, 2, v___f_6556_);
    lean_closure_set(v___f_6558_, 3, v___f_6555_);
    v___x_6559_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
        v_mvarId_6549_,
        v___f_6558_,
        v_a_6550_,
        v_a_6551_,
        v_a_6552_,
        v_a_6553_,
    );
    return v___x_6559_;
}
pub unsafe fn l_Lean_MVarId_getNondepPropHyps___boxed(
    mut v_mvarId_6560_: *mut LeanObject,
    mut v_a_6561_: *mut LeanObject,
    mut v_a_6562_: *mut LeanObject,
    mut v_a_6563_: *mut LeanObject,
    mut v_a_6564_: *mut LeanObject,
    mut v_a_6565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6566_: *mut LeanObject = core::ptr::null_mut();
    v_res_6566_ =
        l_Lean_MVarId_getNondepPropHyps(v_mvarId_6560_, v_a_6561_, v_a_6562_, v_a_6563_, v_a_6564_);
    lean_dec(v_a_6564_);
    lean_dec_ref(v_a_6563_);
    lean_dec(v_a_6562_);
    lean_dec_ref(v_a_6561_);
    return v_res_6566_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(
    mut v_00_u03b2_6567_: *mut LeanObject,
    mut v_m_6568_: *mut LeanObject,
    mut v_a_6569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6570_: *mut LeanObject = core::ptr::null_mut();
    v___x_6570_ = l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___redArg(v_m_6568_, v_a_6569_);
    return v___x_6570_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0___boxed(
    mut v_00_u03b2_6571_: *mut LeanObject,
    mut v_m_6572_: *mut LeanObject,
    mut v_a_6573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6574_: *mut LeanObject = core::ptr::null_mut();
    v_res_6574_ =
        l_Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0(
            v_00_u03b2_6571_,
            v_m_6572_,
            v_a_6573_,
        );
    lean_dec(v_a_6573_);
    return v_res_6574_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2(
    mut v_00_u03b2_6575_: *mut LeanObject,
    mut v_m_6576_: *mut LeanObject,
    mut v_a_6577_: *mut LeanObject,
    mut v_b_6578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6579_: *mut LeanObject = core::ptr::null_mut();
    v___x_6579_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2___redArg(v_m_6576_, v_a_6577_, v_b_6578_);
    return v___x_6579_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(
    mut v_00_u03b2_6580_: *mut LeanObject,
    mut v_m_6581_: *mut LeanObject,
    mut v_a_6582_: *mut LeanObject,
) -> u8 {
    let mut v___x_6583_: u8 = 0;
    v___x_6583_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___redArg(v_m_6581_, v_a_6582_);
    return v___x_6583_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4___boxed(
    mut v_00_u03b2_6584_: *mut LeanObject,
    mut v_m_6585_: *mut LeanObject,
    mut v_a_6586_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6587_: u8 = 0;
    let mut v_r_6588_: *mut LeanObject = core::ptr::null_mut();
    v_res_6587_ =
        l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_MVarId_getNondepPropHyps_spec__4(
            v_00_u03b2_6584_,
            v_m_6585_,
            v_a_6586_,
        );
    lean_dec(v_a_6586_);
    lean_dec_ref(v_m_6585_);
    v_r_6588_ = lean_box((v_res_6587_) as usize);
    return v_r_6588_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(
    mut v_00_u03b2_6589_: *mut LeanObject,
    mut v_a_6590_: *mut LeanObject,
    mut v_x_6591_: *mut LeanObject,
) -> u8 {
    let mut v___x_6592_: u8 = 0;
    v___x_6592_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___redArg(v_a_6590_, v_x_6591_);
    return v___x_6592_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0___boxed(
    mut v_00_u03b2_6593_: *mut LeanObject,
    mut v_a_6594_: *mut LeanObject,
    mut v_x_6595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6596_: u8 = 0;
    let mut v_r_6597_: *mut LeanObject = core::ptr::null_mut();
    v_res_6596_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__0(v_00_u03b2_6593_, v_a_6594_, v_x_6595_);
    lean_dec(v_x_6595_);
    lean_dec(v_a_6594_);
    v_r_6597_ = lean_box((v_res_6596_) as usize);
    return v_r_6597_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(
    mut v_00_u03b2_6598_: *mut LeanObject,
    mut v_a_6599_: *mut LeanObject,
    mut v_x_6600_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6601_: *mut LeanObject = core::ptr::null_mut();
    v___x_6601_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___redArg(v_a_6599_, v_x_6600_);
    return v___x_6601_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1___boxed(
    mut v_00_u03b2_6602_: *mut LeanObject,
    mut v_a_6603_: *mut LeanObject,
    mut v_x_6604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6605_: *mut LeanObject = core::ptr::null_mut();
    v_res_6605_ = l_Std_DHashMap_Internal_AssocList_erase___at___00Std_DHashMap_Internal_Raw_u2080_erase___at___00Lean_MVarId_getNondepPropHyps_spec__0_spec__1(v_00_u03b2_6602_, v_a_6603_, v_x_6604_);
    lean_dec(v_a_6603_);
    return v_res_6605_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(
    mut v_e_6606_: *mut LeanObject,
    mut v_a_6607_: *mut LeanObject,
    mut v___y_6608_: *mut LeanObject,
    mut v___y_6609_: *mut LeanObject,
    mut v___y_6610_: *mut LeanObject,
    mut v___y_6611_: *mut LeanObject,
    mut v___y_6612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6614_: *mut LeanObject = core::ptr::null_mut();
    v___x_6614_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___redArg(v_e_6606_, v_a_6607_);
    return v___x_6614_;
}
pub unsafe fn l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4___boxed(
    mut v_e_6615_: *mut LeanObject,
    mut v_a_6616_: *mut LeanObject,
    mut v___y_6617_: *mut LeanObject,
    mut v___y_6618_: *mut LeanObject,
    mut v___y_6619_: *mut LeanObject,
    mut v___y_6620_: *mut LeanObject,
    mut v___y_6621_: *mut LeanObject,
    mut v___y_6622_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6623_: *mut LeanObject = core::ptr::null_mut();
    v_res_6623_ = l_Lean_ForEachExprWhere_visited___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__4(v_e_6615_, v_a_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_);
    lean_dec(v___y_6621_);
    lean_dec_ref(v___y_6620_);
    lean_dec(v___y_6619_);
    lean_dec_ref(v___y_6618_);
    lean_dec(v___y_6617_);
    lean_dec(v_a_6616_);
    return v_res_6623_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5(
    mut v_00_u03b2_6624_: *mut LeanObject,
    mut v_data_6625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6626_: *mut LeanObject = core::ptr::null_mut();
    v___x_6626_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5___redArg(v_data_6625_);
    return v___x_6626_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(
    mut v_e_6627_: *mut LeanObject,
    mut v_a_6628_: *mut LeanObject,
    mut v___y_6629_: *mut LeanObject,
    mut v___y_6630_: *mut LeanObject,
    mut v___y_6631_: *mut LeanObject,
    mut v___y_6632_: *mut LeanObject,
    mut v___y_6633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6635_: *mut LeanObject = core::ptr::null_mut();
    v___x_6635_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___redArg(v_e_6627_, v_a_6628_);
    return v___x_6635_;
}
pub unsafe fn l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5___boxed(
    mut v_e_6636_: *mut LeanObject,
    mut v_a_6637_: *mut LeanObject,
    mut v___y_6638_: *mut LeanObject,
    mut v___y_6639_: *mut LeanObject,
    mut v___y_6640_: *mut LeanObject,
    mut v___y_6641_: *mut LeanObject,
    mut v___y_6642_: *mut LeanObject,
    mut v___y_6643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6644_: *mut LeanObject = core::ptr::null_mut();
    v_res_6644_ = l_Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5(v_e_6636_, v_a_6637_, v___y_6638_, v___y_6639_, v___y_6640_, v___y_6641_, v___y_6642_);
    lean_dec(v___y_6642_);
    lean_dec_ref(v___y_6641_);
    lean_dec(v___y_6640_);
    lean_dec_ref(v___y_6639_);
    lean_dec(v___y_6638_);
    lean_dec(v_a_6637_);
    return v_res_6644_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8(
    mut v_00_u03b2_6645_: *mut LeanObject,
    mut v_i_6646_: *mut LeanObject,
    mut v_source_6647_: *mut LeanObject,
    mut v_target_6648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    v___x_6649_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8___redArg(v_i_6646_, v_source_6647_, v_target_6648_);
    return v___x_6649_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(
    mut v_a_6650_: *mut LeanObject,
    mut v_as_6651_: *mut LeanObject,
    mut v_sz_6652_: usize,
    mut v_i_6653_: usize,
    mut v_b_6654_: *mut LeanObject,
    mut v___y_6655_: *mut LeanObject,
    mut v___y_6656_: *mut LeanObject,
    mut v___y_6657_: *mut LeanObject,
    mut v___y_6658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6660_: *mut LeanObject = core::ptr::null_mut();
    v___x_6660_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___redArg(v_a_6650_, v_as_6651_, v_sz_6652_, v_i_6653_, v_b_6654_);
    return v___x_6660_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21___boxed(
    mut v_a_6661_: *mut LeanObject,
    mut v_as_6662_: *mut LeanObject,
    mut v_sz_6663_: *mut LeanObject,
    mut v_i_6664_: *mut LeanObject,
    mut v_b_6665_: *mut LeanObject,
    mut v___y_6666_: *mut LeanObject,
    mut v___y_6667_: *mut LeanObject,
    mut v___y_6668_: *mut LeanObject,
    mut v___y_6669_: *mut LeanObject,
    mut v___y_6670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6671_: usize = 0;
    let mut v_i_boxed_6672_: usize = 0;
    let mut v_res_6673_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6671_ = lean_unbox_usize(v_sz_6663_);
    lean_dec(v_sz_6663_);
    v_i_boxed_6672_ = lean_unbox_usize(v_i_6664_);
    lean_dec(v_i_6664_);
    v_res_6673_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__12_spec__21(v_a_6661_, v_as_6662_, v_sz_boxed_6671_, v_i_boxed_6672_, v_b_6665_, v___y_6666_, v___y_6667_, v___y_6668_, v___y_6669_);
    lean_dec(v___y_6669_);
    lean_dec_ref(v___y_6668_);
    lean_dec(v___y_6667_);
    lean_dec_ref(v___y_6666_);
    lean_dec_ref(v_as_6662_);
    lean_dec_ref(v_a_6661_);
    return v_res_6673_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(
    mut v_00_u03b2_6674_: *mut LeanObject,
    mut v_m_6675_: *mut LeanObject,
    mut v_a_6676_: *mut LeanObject,
) -> u8 {
    let mut v___x_6677_: u8 = 0;
    v___x_6677_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___redArg(v_m_6675_, v_a_6676_);
    return v___x_6677_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10___boxed(
    mut v_00_u03b2_6678_: *mut LeanObject,
    mut v_m_6679_: *mut LeanObject,
    mut v_a_6680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6681_: u8 = 0;
    let mut v_r_6682_: *mut LeanObject = core::ptr::null_mut();
    v_res_6681_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10(v_00_u03b2_6678_, v_m_6679_, v_a_6680_);
    lean_dec_ref(v_a_6680_);
    lean_dec_ref(v_m_6679_);
    v_r_6682_ = lean_box((v_res_6681_) as usize);
    return v_r_6682_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11(
    mut v_00_u03b2_6683_: *mut LeanObject,
    mut v_m_6684_: *mut LeanObject,
    mut v_a_6685_: *mut LeanObject,
    mut v_b_6686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    v___x_6687_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11___redArg(v_m_6684_, v_a_6685_, v_b_6686_);
    return v___x_6687_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14(
    mut v_00_u03b2_6688_: *mut LeanObject,
    mut v_x_6689_: *mut LeanObject,
    mut v_x_6690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6691_: *mut LeanObject = core::ptr::null_mut();
    v___x_6691_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_MVarId_getNondepPropHyps_spec__2_spec__5_spec__8_spec__14___redArg(v_x_6689_, v_x_6690_);
    return v___x_6691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(
    mut v_a_6692_: *mut LeanObject,
    mut v_as_6693_: *mut LeanObject,
    mut v_sz_6694_: usize,
    mut v_i_6695_: usize,
    mut v_b_6696_: *mut LeanObject,
    mut v___y_6697_: *mut LeanObject,
    mut v___y_6698_: *mut LeanObject,
    mut v___y_6699_: *mut LeanObject,
    mut v___y_6700_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6702_: *mut LeanObject = core::ptr::null_mut();
    v___x_6702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___redArg(v_a_6692_, v_as_6693_, v_sz_6694_, v_i_6695_, v_b_6696_);
    return v___x_6702_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24___boxed(
    mut v_a_6703_: *mut LeanObject,
    mut v_as_6704_: *mut LeanObject,
    mut v_sz_6705_: *mut LeanObject,
    mut v_i_6706_: *mut LeanObject,
    mut v_b_6707_: *mut LeanObject,
    mut v___y_6708_: *mut LeanObject,
    mut v___y_6709_: *mut LeanObject,
    mut v___y_6710_: *mut LeanObject,
    mut v___y_6711_: *mut LeanObject,
    mut v___y_6712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6713_: usize = 0;
    let mut v_i_boxed_6714_: usize = 0;
    let mut v_res_6715_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6713_ = lean_unbox_usize(v_sz_6705_);
    lean_dec(v_sz_6705_);
    v_i_boxed_6714_ = lean_unbox_usize(v_i_6706_);
    lean_dec(v_i_6706_);
    v_res_6715_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_getNondepPropHyps_spec__5_spec__11_spec__19_spec__24(v_a_6703_, v_as_6704_, v_sz_boxed_6713_, v_i_boxed_6714_, v_b_6707_, v___y_6708_, v___y_6709_, v___y_6710_, v___y_6711_);
    lean_dec(v___y_6711_);
    lean_dec_ref(v___y_6710_);
    lean_dec(v___y_6709_);
    lean_dec_ref(v___y_6708_);
    lean_dec_ref(v_as_6704_);
    lean_dec_ref(v_a_6703_);
    return v_res_6715_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(
    mut v_00_u03b2_6716_: *mut LeanObject,
    mut v_a_6717_: *mut LeanObject,
    mut v_x_6718_: *mut LeanObject,
) -> u8 {
    let mut v___x_6719_: u8 = 0;
    v___x_6719_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___redArg(v_a_6717_, v_x_6718_);
    return v___x_6719_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16___boxed(
    mut v_00_u03b2_6720_: *mut LeanObject,
    mut v_a_6721_: *mut LeanObject,
    mut v_x_6722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6723_: u8 = 0;
    let mut v_r_6724_: *mut LeanObject = core::ptr::null_mut();
    v_res_6723_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__10_spec__16(v_00_u03b2_6720_, v_a_6721_, v_x_6722_);
    lean_dec(v_x_6722_);
    lean_dec_ref(v_a_6721_);
    v_r_6724_ = lean_box((v_res_6723_) as usize);
    return v_r_6724_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18(
    mut v_00_u03b2_6725_: *mut LeanObject,
    mut v_data_6726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6727_: *mut LeanObject = core::ptr::null_mut();
    v___x_6727_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18___redArg(v_data_6726_);
    return v___x_6727_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26(
    mut v_00_u03b2_6728_: *mut LeanObject,
    mut v_i_6729_: *mut LeanObject,
    mut v_source_6730_: *mut LeanObject,
    mut v_target_6731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6732_: *mut LeanObject = core::ptr::null_mut();
    v___x_6732_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26___redArg(v_i_6729_, v_source_6730_, v_target_6731_);
    return v___x_6732_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30(
    mut v_00_u03b2_6733_: *mut LeanObject,
    mut v_x_6734_: *mut LeanObject,
    mut v_x_6735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6736_: *mut LeanObject = core::ptr::null_mut();
    v___x_6736_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_ForEachExprWhere_checked___at___00__private_Lean_Util_ForEachExprWhere_0__Lean_ForEachExprWhere_visit_go___at___00Lean_ForEachExprWhere_visit___at___00Lean_MVarId_getNondepPropHyps_spec__1_spec__3_spec__5_spec__11_spec__18_spec__26_spec__30___redArg(v_x_6734_, v_x_6735_);
    return v___x_6736_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6743_: *mut LeanObject = core::ptr::null_mut();
    v___x_6742_ = l_Lean_maxRecDepthErrorMessage;
    v___x_6743_ = lean_alloc_ctor(3, 1, (0) as u32);
    lean_ctor_set(v___x_6743_, 0, v___x_6742_);
    return v___x_6743_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4()
-> *mut LeanObject {
    let mut v___x_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    v___x_6744_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__3);
    v___x_6745_ = l_Lean_MessageData_ofFormat(v___x_6744_);
    return v___x_6745_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5()
-> *mut LeanObject {
    let mut v___x_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6748_: *mut LeanObject = core::ptr::null_mut();
    v___x_6746_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__4);
    v___x_6747_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__2;
    v___x_6748_ = lean_alloc_ctor(8, 2, (0) as u32);
    lean_ctor_set(v___x_6748_, 0, v___x_6747_);
    lean_ctor_set(v___x_6748_, 1, v___x_6746_);
    return v___x_6748_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(
    mut v_ref_6749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: *mut LeanObject = core::ptr::null_mut();
    v___x_6751_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___closed__5);
    v___x_6752_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_6752_, 0, v_ref_6749_);
    lean_ctor_set(v___x_6752_, 1, v___x_6751_);
    v___x_6753_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_6753_, 0, v___x_6752_);
    return v___x_6753_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg___boxed(
    mut v_ref_6754_: *mut LeanObject,
    mut v___y_6755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6756_: *mut LeanObject = core::ptr::null_mut();
    v_res_6756_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_6754_);
    return v_res_6756_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(
    mut v_00_u03b1_6757_: *mut LeanObject,
    mut v_ref_6758_: *mut LeanObject,
    mut v___y_6759_: *mut LeanObject,
    mut v___y_6760_: *mut LeanObject,
    mut v___y_6761_: *mut LeanObject,
    mut v___y_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    v___x_6765_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_6758_);
    return v___x_6765_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___boxed(
    mut v_00_u03b1_6766_: *mut LeanObject,
    mut v_ref_6767_: *mut LeanObject,
    mut v___y_6768_: *mut LeanObject,
    mut v___y_6769_: *mut LeanObject,
    mut v___y_6770_: *mut LeanObject,
    mut v___y_6771_: *mut LeanObject,
    mut v___y_6772_: *mut LeanObject,
    mut v___y_6773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6774_: *mut LeanObject = core::ptr::null_mut();
    v_res_6774_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1(v_00_u03b1_6766_, v_ref_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_);
    lean_dec(v___y_6772_);
    lean_dec_ref(v___y_6771_);
    lean_dec(v___y_6770_);
    lean_dec_ref(v___y_6769_);
    lean_dec(v___y_6768_);
    return v_res_6774_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(
    mut v_x_6775_: *mut LeanObject,
    mut v_mvarId_6776_: *mut LeanObject,
    mut v_a_6777_: *mut LeanObject,
    mut v_a_6778_: *mut LeanObject,
    mut v_a_6779_: *mut LeanObject,
    mut v_a_6780_: *mut LeanObject,
    mut v_a_6781_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fileName_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6795_: u8 = 0;
    let mut v_cancelTk_x3f_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6797_: u8 = 0;
    let mut v_inheritedTraceOptions_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6807_: u8 = 0;
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6817_: u8 = 0;
    let mut v_a_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6821_: u8 = 0;
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6825_: u8 = 0;
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: u8 = 0;
    let mut v___x_6828_: u8 = 0;
    let mut v___x_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6783_ = lean_ctor_get(v_a_6780_, 0);
                v_fileMap_6784_ = lean_ctor_get(v_a_6780_, 1);
                v_options_6785_ = lean_ctor_get(v_a_6780_, 2);
                v_currRecDepth_6786_ = lean_ctor_get(v_a_6780_, 3);
                v_maxRecDepth_6787_ = lean_ctor_get(v_a_6780_, 4);
                v_ref_6788_ = lean_ctor_get(v_a_6780_, 5);
                v_currNamespace_6789_ = lean_ctor_get(v_a_6780_, 6);
                v_openDecls_6790_ = lean_ctor_get(v_a_6780_, 7);
                v_initHeartbeats_6791_ = lean_ctor_get(v_a_6780_, 8);
                v_maxHeartbeats_6792_ = lean_ctor_get(v_a_6780_, 9);
                v_quotContext_6793_ = lean_ctor_get(v_a_6780_, 10);
                v_currMacroScope_6794_ = lean_ctor_get(v_a_6780_, 11);
                v_diag_6795_ = lean_ctor_get_uint8(
                    v_a_6780_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6796_ = lean_ctor_get(v_a_6780_, 12);
                v_suppressElabErrors_6797_ = lean_ctor_get_uint8(
                    v_a_6780_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6798_ = lean_ctor_get(v_a_6780_, 13);
                v___x_6826_ = lean_unsigned_to_nat(0);
                v___x_6827_ = lean_nat_dec_eq(v_maxRecDepth_6787_, v___x_6826_);
                if v___x_6827_ == 0 {
                    v___x_6828_ = lean_nat_dec_eq(v_currRecDepth_6786_, v_maxRecDepth_6787_);
                    if v___x_6828_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_mvarId_6776_);
                        lean_dec_ref(v_x_6775_);
                        lean_inc(v_ref_6788_);
                        v___x_6829_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__1___redArg(v_ref_6788_);
                        return v___x_6829_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6800_ = lean_unsigned_to_nat(1);
                v___x_6801_ = lean_nat_add(v_currRecDepth_6786_, v___x_6800_);
                lean_inc_ref(v_inheritedTraceOptions_6798_);
                lean_inc(v_cancelTk_x3f_6796_);
                lean_inc(v_currMacroScope_6794_);
                lean_inc(v_quotContext_6793_);
                lean_inc(v_maxHeartbeats_6792_);
                lean_inc(v_initHeartbeats_6791_);
                lean_inc(v_openDecls_6790_);
                lean_inc(v_currNamespace_6789_);
                lean_inc(v_ref_6788_);
                lean_inc(v_maxRecDepth_6787_);
                lean_inc_ref(v_options_6785_);
                lean_inc_ref(v_fileMap_6784_);
                lean_inc_ref(v_fileName_6783_);
                v___x_6802_ = lean_alloc_ctor(0, 14, (2) as u32);
                lean_ctor_set(v___x_6802_, 0, v_fileName_6783_);
                lean_ctor_set(v___x_6802_, 1, v_fileMap_6784_);
                lean_ctor_set(v___x_6802_, 2, v_options_6785_);
                lean_ctor_set(v___x_6802_, 3, v___x_6801_);
                lean_ctor_set(v___x_6802_, 4, v_maxRecDepth_6787_);
                lean_ctor_set(v___x_6802_, 5, v_ref_6788_);
                lean_ctor_set(v___x_6802_, 6, v_currNamespace_6789_);
                lean_ctor_set(v___x_6802_, 7, v_openDecls_6790_);
                lean_ctor_set(v___x_6802_, 8, v_initHeartbeats_6791_);
                lean_ctor_set(v___x_6802_, 9, v_maxHeartbeats_6792_);
                lean_ctor_set(v___x_6802_, 10, v_quotContext_6793_);
                lean_ctor_set(v___x_6802_, 11, v_currMacroScope_6794_);
                lean_ctor_set(v___x_6802_, 12, v_cancelTk_x3f_6796_);
                lean_ctor_set(v___x_6802_, 13, v_inheritedTraceOptions_6798_);
                lean_ctor_set_uint8(
                    v___x_6802_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                    v_diag_6795_,
                );
                lean_ctor_set_uint8(
                    v___x_6802_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_6797_,
                );
                lean_inc_ref(v_x_6775_);
                lean_inc(v_a_6781_);
                lean_inc_ref(v___x_6802_);
                lean_inc(v_a_6779_);
                lean_inc_ref(v_a_6778_);
                lean_inc(v_mvarId_6776_);
                v___x_6803_ = lean_apply_6(
                    v_x_6775_,
                    v_mvarId_6776_,
                    v_a_6778_,
                    v_a_6779_,
                    v___x_6802_,
                    v_a_6781_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6803_) == 0 {
                    v_a_6804_ = lean_ctor_get(v___x_6803_, 0);
                    v_isSharedCheck_6817_ = (!lean_is_exclusive(v___x_6803_)) as u8;
                    if v_isSharedCheck_6817_ == 0 {
                        v___x_6806_ = v___x_6803_;
                        v_isShared_6807_ = v_isSharedCheck_6817_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6804_);
                        lean_dec(v___x_6803_);
                        v___x_6806_ = lean_box(0);
                        v_isShared_6807_ = v_isSharedCheck_6817_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_6802_, 14);
                    lean_dec(v_mvarId_6776_);
                    lean_dec_ref(v_x_6775_);
                    v_a_6818_ = lean_ctor_get(v___x_6803_, 0);
                    v_isSharedCheck_6825_ = (!lean_is_exclusive(v___x_6803_)) as u8;
                    if v_isSharedCheck_6825_ == 0 {
                        v___x_6820_ = v___x_6803_;
                        v_isShared_6821_ = v_isSharedCheck_6825_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_6818_);
                        lean_dec(v___x_6803_);
                        v___x_6820_ = lean_box(0);
                        v_isShared_6821_ = v_isSharedCheck_6825_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6804_) == 0 {
                    lean_dec_ref_known(v___x_6802_, 14);
                    lean_dec_ref(v_x_6775_);
                    v___x_6808_ = lean_st_ref_take(v_a_6777_);
                    v___x_6809_ = lean_array_push(v___x_6808_, v_mvarId_6776_);
                    v___x_6810_ = lean_st_ref_set(v_a_6777_, v___x_6809_);
                    v___x_6811_ = lean_box(0);
                    if v_isShared_6807_ == 0 {
                        lean_ctor_set(v___x_6806_, 0, v___x_6811_);
                        v___x_6813_ = v___x_6806_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6814_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6814_, 0, v___x_6811_);
                        v___x_6813_ = v_reuseFailAlloc_6814_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6806_);
                    lean_dec(v_mvarId_6776_);
                    v_val_6815_ = lean_ctor_get(v_a_6804_, 0);
                    lean_inc(v_val_6815_);
                    lean_dec_ref_known(v_a_6804_, 1);
                    v___x_6816_ = l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(v_x_6775_, v_val_6815_, v_a_6777_, v_a_6778_, v_a_6779_, v___x_6802_, v_a_6781_);
                    lean_dec_ref_known(v___x_6802_, 14);
                    return v___x_6816_;
                }
            }
            3 => {
                return v___x_6813_;
            }
            4 => {
                if v_isShared_6821_ == 0 {
                    v___x_6823_ = v___x_6820_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6824_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6824_, 0, v_a_6818_);
                    v___x_6823_ = v_reuseFailAlloc_6824_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(
    mut v_x_6830_: *mut LeanObject,
    mut v_as_6831_: *mut LeanObject,
    mut v___y_6832_: *mut LeanObject,
    mut v___y_6833_: *mut LeanObject,
    mut v___y_6834_: *mut LeanObject,
    mut v___y_6835_: *mut LeanObject,
    mut v___y_6836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_6831_) == 0 {
                    lean_dec_ref(v_x_6830_);
                    v___x_6838_ = lean_box(0);
                    v___x_6839_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6839_, 0, v___x_6838_);
                    return v___x_6839_;
                } else {
                    v_head_6840_ = lean_ctor_get(v_as_6831_, 0);
                    lean_inc(v_head_6840_);
                    v_tail_6841_ = lean_ctor_get(v_as_6831_, 1);
                    lean_inc(v_tail_6841_);
                    lean_dec_ref_known(v_as_6831_, 2);
                    lean_inc_ref(v_x_6830_);
                    v___x_6842_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(
                        v_x_6830_,
                        v_head_6840_,
                        v___y_6832_,
                        v___y_6833_,
                        v___y_6834_,
                        v___y_6835_,
                        v___y_6836_,
                    );
                    if lean_obj_tag(v___x_6842_) == 0 {
                        lean_dec_ref_known(v___x_6842_, 1);
                        v_as_6831_ = v_tail_6841_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_tail_6841_);
                        lean_dec_ref(v_x_6830_);
                        return v___x_6842_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0___boxed(
    mut v_x_6844_: *mut LeanObject,
    mut v_as_6845_: *mut LeanObject,
    mut v___y_6846_: *mut LeanObject,
    mut v___y_6847_: *mut LeanObject,
    mut v___y_6848_: *mut LeanObject,
    mut v___y_6849_: *mut LeanObject,
    mut v___y_6850_: *mut LeanObject,
    mut v___y_6851_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6852_: *mut LeanObject = core::ptr::null_mut();
    v_res_6852_ =
        l_List_forM___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go_spec__0(
            v_x_6844_,
            v_as_6845_,
            v___y_6846_,
            v___y_6847_,
            v___y_6848_,
            v___y_6849_,
            v___y_6850_,
        );
    lean_dec(v___y_6850_);
    lean_dec_ref(v___y_6849_);
    lean_dec(v___y_6848_);
    lean_dec_ref(v___y_6847_);
    lean_dec(v___y_6846_);
    return v_res_6852_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go___boxed(
    mut v_x_6853_: *mut LeanObject,
    mut v_mvarId_6854_: *mut LeanObject,
    mut v_a_6855_: *mut LeanObject,
    mut v_a_6856_: *mut LeanObject,
    mut v_a_6857_: *mut LeanObject,
    mut v_a_6858_: *mut LeanObject,
    mut v_a_6859_: *mut LeanObject,
    mut v_a_6860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6861_: *mut LeanObject = core::ptr::null_mut();
    v_res_6861_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(
        v_x_6853_,
        v_mvarId_6854_,
        v_a_6855_,
        v_a_6856_,
        v_a_6857_,
        v_a_6858_,
        v_a_6859_,
    );
    lean_dec(v_a_6859_);
    lean_dec_ref(v_a_6858_);
    lean_dec(v_a_6857_);
    lean_dec_ref(v_a_6856_);
    lean_dec(v_a_6855_);
    return v_res_6861_;
}
pub unsafe fn l_Lean_Meta_saturate(
    mut v_mvarId_6862_: *mut LeanObject,
    mut v_x_6863_: *mut LeanObject,
    mut v_a_6864_: *mut LeanObject,
    mut v_a_6865_: *mut LeanObject,
    mut v_a_6866_: *mut LeanObject,
    mut v_a_6867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6874_: u8 = 0;
    let mut v___x_6875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6880_: u8 = 0;
    let mut v_unused_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6885_: u8 = 0;
    let mut v___x_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6869_ = l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0;
                v___x_6870_ = lean_st_mk_ref(v___x_6869_);
                v___x_6871_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_saturate_go(
                    v_x_6863_,
                    v_mvarId_6862_,
                    v___x_6870_,
                    v_a_6864_,
                    v_a_6865_,
                    v_a_6866_,
                    v_a_6867_,
                );
                if lean_obj_tag(v___x_6871_) == 0 {
                    v_isSharedCheck_6880_ = (!lean_is_exclusive(v___x_6871_)) as u8;
                    if v_isSharedCheck_6880_ == 0 {
                        v_unused_6881_ = lean_ctor_get(v___x_6871_, 0);
                        lean_dec(v_unused_6881_);
                        v___x_6873_ = v___x_6871_;
                        v_isShared_6874_ = v_isSharedCheck_6880_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_6871_);
                        v___x_6873_ = lean_box(0);
                        v_isShared_6874_ = v_isSharedCheck_6880_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_6870_);
                    v_a_6882_ = lean_ctor_get(v___x_6871_, 0);
                    v_isSharedCheck_6889_ = (!lean_is_exclusive(v___x_6871_)) as u8;
                    if v_isSharedCheck_6889_ == 0 {
                        v___x_6884_ = v___x_6871_;
                        v_isShared_6885_ = v_isSharedCheck_6889_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6882_);
                        lean_dec(v___x_6871_);
                        v___x_6884_ = lean_box(0);
                        v_isShared_6885_ = v_isSharedCheck_6889_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6875_ = lean_st_ref_get(v___x_6870_);
                lean_dec(v___x_6870_);
                v___x_6876_ = lean_array_to_list(v___x_6875_);
                if v_isShared_6874_ == 0 {
                    lean_ctor_set(v___x_6873_, 0, v___x_6876_);
                    v___x_6878_ = v___x_6873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6879_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6879_, 0, v___x_6876_);
                    v___x_6878_ = v_reuseFailAlloc_6879_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6878_;
            }
            3 => {
                if v_isShared_6885_ == 0 {
                    v___x_6887_ = v___x_6884_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6888_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6888_, 0, v_a_6882_);
                    v___x_6887_ = v_reuseFailAlloc_6888_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_saturate___boxed(
    mut v_mvarId_6890_: *mut LeanObject,
    mut v_x_6891_: *mut LeanObject,
    mut v_a_6892_: *mut LeanObject,
    mut v_a_6893_: *mut LeanObject,
    mut v_a_6894_: *mut LeanObject,
    mut v_a_6895_: *mut LeanObject,
    mut v_a_6896_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6897_: *mut LeanObject = core::ptr::null_mut();
    v_res_6897_ = l_Lean_Meta_saturate(
        v_mvarId_6890_,
        v_x_6891_,
        v_a_6892_,
        v_a_6893_,
        v_a_6894_,
        v_a_6895_,
    );
    lean_dec(v_a_6895_);
    lean_dec_ref(v_a_6894_);
    lean_dec(v_a_6893_);
    lean_dec_ref(v_a_6892_);
    return v_res_6897_;
}
pub unsafe fn l_Lean_Meta_exactlyOne(
    mut v_mvarIds_6898_: *mut LeanObject,
    mut v_msg_6899_: *mut LeanObject,
    mut v_a_6900_: *mut LeanObject,
    mut v_a_6901_: *mut LeanObject,
    mut v_a_6902_: *mut LeanObject,
    mut v_a_6903_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_mvarIds_6898_) == 1 {
        let mut v_tail_6905_: *mut LeanObject = core::ptr::null_mut();
        v_tail_6905_ = lean_ctor_get(v_mvarIds_6898_, 1);
        if lean_obj_tag(v_tail_6905_) == 0 {
            let mut v_head_6906_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6907_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_msg_6899_);
            v_head_6906_ = lean_ctor_get(v_mvarIds_6898_, 0);
            lean_inc(v_head_6906_);
            v___x_6907_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_6907_, 0, v_head_6906_);
            return v___x_6907_;
        } else {
            let mut v___x_6908_: *mut LeanObject = core::ptr::null_mut();
            v___x_6908_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
                v_msg_6899_,
                v_a_6900_,
                v_a_6901_,
                v_a_6902_,
                v_a_6903_,
            );
            return v___x_6908_;
        }
    } else {
        let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
        v___x_6909_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
            v_msg_6899_,
            v_a_6900_,
            v_a_6901_,
            v_a_6902_,
            v_a_6903_,
        );
        return v___x_6909_;
    }
}
pub unsafe fn l_Lean_Meta_exactlyOne___boxed(
    mut v_mvarIds_6910_: *mut LeanObject,
    mut v_msg_6911_: *mut LeanObject,
    mut v_a_6912_: *mut LeanObject,
    mut v_a_6913_: *mut LeanObject,
    mut v_a_6914_: *mut LeanObject,
    mut v_a_6915_: *mut LeanObject,
    mut v_a_6916_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6917_: *mut LeanObject = core::ptr::null_mut();
    v_res_6917_ = l_Lean_Meta_exactlyOne(
        v_mvarIds_6910_,
        v_msg_6911_,
        v_a_6912_,
        v_a_6913_,
        v_a_6914_,
        v_a_6915_,
    );
    lean_dec(v_a_6915_);
    lean_dec_ref(v_a_6914_);
    lean_dec(v_a_6913_);
    lean_dec_ref(v_a_6912_);
    lean_dec(v_mvarIds_6910_);
    return v_res_6917_;
}
pub unsafe fn l_Lean_Meta_ensureAtMostOne(
    mut v_mvarIds_6918_: *mut LeanObject,
    mut v_msg_6919_: *mut LeanObject,
    mut v_a_6920_: *mut LeanObject,
    mut v_a_6921_: *mut LeanObject,
    mut v_a_6922_: *mut LeanObject,
    mut v_a_6923_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_mvarIds_6918_) == 0 {
        let mut v___x_6925_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_6926_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_msg_6919_);
        v___x_6925_ = lean_box(0);
        v___x_6926_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_6926_, 0, v___x_6925_);
        return v___x_6926_;
    } else {
        let mut v_tail_6927_: *mut LeanObject = core::ptr::null_mut();
        v_tail_6927_ = lean_ctor_get(v_mvarIds_6918_, 1);
        if lean_obj_tag(v_tail_6927_) == 0 {
            let mut v_head_6928_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6929_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref(v_msg_6919_);
            v_head_6928_ = lean_ctor_get(v_mvarIds_6918_, 0);
            lean_inc(v_head_6928_);
            v___x_6929_ = lean_alloc_ctor(1, 1, (0) as u32);
            lean_ctor_set(v___x_6929_, 0, v_head_6928_);
            v___x_6930_ = lean_alloc_ctor(0, 1, (0) as u32);
            lean_ctor_set(v___x_6930_, 0, v___x_6929_);
            return v___x_6930_;
        } else {
            let mut v___x_6931_: *mut LeanObject = core::ptr::null_mut();
            v___x_6931_ = l_Lean_throwError___at___00Lean_Meta_throwTacticEx_spec__0___redArg(
                v_msg_6919_,
                v_a_6920_,
                v_a_6921_,
                v_a_6922_,
                v_a_6923_,
            );
            return v___x_6931_;
        }
    }
}
pub unsafe fn l_Lean_Meta_ensureAtMostOne___boxed(
    mut v_mvarIds_6932_: *mut LeanObject,
    mut v_msg_6933_: *mut LeanObject,
    mut v_a_6934_: *mut LeanObject,
    mut v_a_6935_: *mut LeanObject,
    mut v_a_6936_: *mut LeanObject,
    mut v_a_6937_: *mut LeanObject,
    mut v_a_6938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6939_: *mut LeanObject = core::ptr::null_mut();
    v_res_6939_ = l_Lean_Meta_ensureAtMostOne(
        v_mvarIds_6932_,
        v_msg_6933_,
        v_a_6934_,
        v_a_6935_,
        v_a_6936_,
        v_a_6937_,
    );
    lean_dec(v_a_6937_);
    lean_dec_ref(v_a_6936_);
    lean_dec(v_a_6935_);
    lean_dec_ref(v_a_6934_);
    lean_dec(v_mvarIds_6932_);
    return v_res_6939_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(
    mut v_as_6940_: *mut LeanObject,
    mut v_sz_6941_: usize,
    mut v_i_6942_: usize,
    mut v_b_6943_: *mut LeanObject,
    mut v___y_6944_: *mut LeanObject,
    mut v___y_6945_: *mut LeanObject,
    mut v___y_6946_: *mut LeanObject,
    mut v___y_6947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6949_: u8 = 0;
    let mut v___x_6950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6954_: u8 = 0;
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: usize = 0;
    let mut v___x_6961_: usize = 0;
    let mut v_reuseFailAlloc_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6966_: u8 = 0;
    let mut v___x_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6970_: u8 = 0;
    let mut v___x_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6976_: u8 = 0;
    let mut v___x_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6980_: u8 = 0;
    let mut v_isSharedCheck_6981_: u8 = 0;
    let mut v_unused_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6949_ = lean_usize_dec_lt(v_i_6942_, v_sz_6941_);
                if v___x_6949_ == 0 {
                    v___x_6950_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6950_, 0, v_b_6943_);
                    return v___x_6950_;
                } else {
                    v_snd_6951_ = lean_ctor_get(v_b_6943_, 1);
                    v_isSharedCheck_6981_ = (!lean_is_exclusive(v_b_6943_)) as u8;
                    if v_isSharedCheck_6981_ == 0 {
                        v_unused_6982_ = lean_ctor_get(v_b_6943_, 0);
                        lean_dec(v_unused_6982_);
                        v___x_6953_ = v_b_6943_;
                        v_isShared_6954_ = v_isSharedCheck_6981_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6951_);
                        lean_dec(v_b_6943_);
                        v___x_6953_ = lean_box(0);
                        v_isShared_6954_ = v_isSharedCheck_6981_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6955_ = lean_box(0);
                v_a_6964_ = lean_array_uget_borrowed(v_as_6940_, v_i_6942_);
                if lean_obj_tag(v_a_6964_) == 0 {
                    v_a_6957_ = v_snd_6951_;
                    state = 2;
                    continue;
                } else {
                    v_val_6965_ = lean_ctor_get(v_a_6964_, 0);
                    v___x_6966_ = l_Lean_LocalDecl_isImplementationDetail(v_val_6965_);
                    if v___x_6966_ == 0 {
                        v___x_6967_ = l_Lean_LocalDecl_type(v_val_6965_);
                        v___x_6968_ = l_Lean_Meta_isProp(
                            v___x_6967_,
                            v___y_6944_,
                            v___y_6945_,
                            v___y_6946_,
                            v___y_6947_,
                        );
                        if lean_obj_tag(v___x_6968_) == 0 {
                            v_a_6969_ = lean_ctor_get(v___x_6968_, 0);
                            lean_inc(v_a_6969_);
                            lean_dec_ref_known(v___x_6968_, 1);
                            v___x_6970_ = (lean_unbox(v_a_6969_) as u8);
                            lean_dec(v_a_6969_);
                            if v___x_6970_ == 0 {
                                v_a_6957_ = v_snd_6951_;
                                state = 2;
                                continue;
                            } else {
                                v___x_6971_ = l_Lean_LocalDecl_fvarId(v_val_6965_);
                                v___x_6972_ = lean_array_push(v_snd_6951_, v___x_6971_);
                                v_a_6957_ = v___x_6972_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_6953_);
                            lean_dec(v_snd_6951_);
                            v_a_6973_ = lean_ctor_get(v___x_6968_, 0);
                            v_isSharedCheck_6980_ = (!lean_is_exclusive(v___x_6968_)) as u8;
                            if v_isSharedCheck_6980_ == 0 {
                                v___x_6975_ = v___x_6968_;
                                v_isShared_6976_ = v_isSharedCheck_6980_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_6973_);
                                lean_dec(v___x_6968_);
                                v___x_6975_ = lean_box(0);
                                v_isShared_6976_ = v_isSharedCheck_6980_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_6957_ = v_snd_6951_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6954_ == 0 {
                    lean_ctor_set(v___x_6953_, 1, v_a_6957_);
                    lean_ctor_set(v___x_6953_, 0, v___x_6955_);
                    v___x_6959_ = v___x_6953_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6963_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6963_, 0, v___x_6955_);
                    lean_ctor_set(v_reuseFailAlloc_6963_, 1, v_a_6957_);
                    v___x_6959_ = v_reuseFailAlloc_6963_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6960_ = 1usize;
                v___x_6961_ = lean_usize_add(v_i_6942_, v___x_6960_);
                v_i_6942_ = v___x_6961_;
                v_b_6943_ = v___x_6959_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_6976_ == 0 {
                    v___x_6978_ = v___x_6975_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6979_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6979_, 0, v_a_6973_);
                    v___x_6978_ = v_reuseFailAlloc_6979_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6978_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_as_6983_: *mut LeanObject,
    mut v_sz_6984_: *mut LeanObject,
    mut v_i_6985_: *mut LeanObject,
    mut v_b_6986_: *mut LeanObject,
    mut v___y_6987_: *mut LeanObject,
    mut v___y_6988_: *mut LeanObject,
    mut v___y_6989_: *mut LeanObject,
    mut v___y_6990_: *mut LeanObject,
    mut v___y_6991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6992_: usize = 0;
    let mut v_i_boxed_6993_: usize = 0;
    let mut v_res_6994_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6992_ = lean_unbox_usize(v_sz_6984_);
    lean_dec(v_sz_6984_);
    v_i_boxed_6993_ = lean_unbox_usize(v_i_6985_);
    lean_dec(v_i_6985_);
    v_res_6994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_6983_, v_sz_boxed_6992_, v_i_boxed_6993_, v_b_6986_, v___y_6987_, v___y_6988_, v___y_6989_, v___y_6990_);
    lean_dec(v___y_6990_);
    lean_dec_ref(v___y_6989_);
    lean_dec(v___y_6988_);
    lean_dec_ref(v___y_6987_);
    lean_dec_ref(v_as_6983_);
    return v_res_6994_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(
    mut v_as_6995_: *mut LeanObject,
    mut v_sz_6996_: usize,
    mut v_i_6997_: usize,
    mut v_b_6998_: *mut LeanObject,
    mut v___y_6999_: *mut LeanObject,
    mut v___y_7000_: *mut LeanObject,
    mut v___y_7001_: *mut LeanObject,
    mut v___y_7002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7004_: u8 = 0;
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7009_: u8 = 0;
    let mut v___x_7010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7015_: usize = 0;
    let mut v___x_7016_: usize = 0;
    let mut v___x_7017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7021_: u8 = 0;
    let mut v___x_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7025_: u8 = 0;
    let mut v___x_7026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7031_: u8 = 0;
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7035_: u8 = 0;
    let mut v_isSharedCheck_7036_: u8 = 0;
    let mut v_unused_7037_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7004_ = lean_usize_dec_lt(v_i_6997_, v_sz_6996_);
                if v___x_7004_ == 0 {
                    v___x_7005_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7005_, 0, v_b_6998_);
                    return v___x_7005_;
                } else {
                    v_snd_7006_ = lean_ctor_get(v_b_6998_, 1);
                    v_isSharedCheck_7036_ = (!lean_is_exclusive(v_b_6998_)) as u8;
                    if v_isSharedCheck_7036_ == 0 {
                        v_unused_7037_ = lean_ctor_get(v_b_6998_, 0);
                        lean_dec(v_unused_7037_);
                        v___x_7008_ = v_b_6998_;
                        v_isShared_7009_ = v_isSharedCheck_7036_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7006_);
                        lean_dec(v_b_6998_);
                        v___x_7008_ = lean_box(0);
                        v_isShared_7009_ = v_isSharedCheck_7036_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7010_ = lean_box(0);
                v_a_7019_ = lean_array_uget_borrowed(v_as_6995_, v_i_6997_);
                if lean_obj_tag(v_a_7019_) == 0 {
                    v_a_7012_ = v_snd_7006_;
                    state = 2;
                    continue;
                } else {
                    v_val_7020_ = lean_ctor_get(v_a_7019_, 0);
                    v___x_7021_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7020_);
                    if v___x_7021_ == 0 {
                        v___x_7022_ = l_Lean_LocalDecl_type(v_val_7020_);
                        v___x_7023_ = l_Lean_Meta_isProp(
                            v___x_7022_,
                            v___y_6999_,
                            v___y_7000_,
                            v___y_7001_,
                            v___y_7002_,
                        );
                        if lean_obj_tag(v___x_7023_) == 0 {
                            v_a_7024_ = lean_ctor_get(v___x_7023_, 0);
                            lean_inc(v_a_7024_);
                            lean_dec_ref_known(v___x_7023_, 1);
                            v___x_7025_ = (lean_unbox(v_a_7024_) as u8);
                            lean_dec(v_a_7024_);
                            if v___x_7025_ == 0 {
                                v_a_7012_ = v_snd_7006_;
                                state = 2;
                                continue;
                            } else {
                                v___x_7026_ = l_Lean_LocalDecl_fvarId(v_val_7020_);
                                v___x_7027_ = lean_array_push(v_snd_7006_, v___x_7026_);
                                v_a_7012_ = v___x_7027_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7008_);
                            lean_dec(v_snd_7006_);
                            v_a_7028_ = lean_ctor_get(v___x_7023_, 0);
                            v_isSharedCheck_7035_ = (!lean_is_exclusive(v___x_7023_)) as u8;
                            if v_isSharedCheck_7035_ == 0 {
                                v___x_7030_ = v___x_7023_;
                                v_isShared_7031_ = v_isSharedCheck_7035_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_7028_);
                                lean_dec(v___x_7023_);
                                v___x_7030_ = lean_box(0);
                                v_isShared_7031_ = v_isSharedCheck_7035_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_7012_ = v_snd_7006_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7009_ == 0 {
                    lean_ctor_set(v___x_7008_, 1, v_a_7012_);
                    lean_ctor_set(v___x_7008_, 0, v___x_7010_);
                    v___x_7014_ = v___x_7008_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7018_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7018_, 0, v___x_7010_);
                    lean_ctor_set(v_reuseFailAlloc_7018_, 1, v_a_7012_);
                    v___x_7014_ = v_reuseFailAlloc_7018_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7015_ = 1usize;
                v___x_7016_ = lean_usize_add(v_i_6997_, v___x_7015_);
                v___x_7017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2_spec__3(v_as_6995_, v_sz_6996_, v___x_7016_, v___x_7014_, v___y_6999_, v___y_7000_, v___y_7001_, v___y_7002_);
                return v___x_7017_;
            }
            4 => {
                if v_isShared_7031_ == 0 {
                    v___x_7033_ = v___x_7030_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7034_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7034_, 0, v_a_7028_);
                    v___x_7033_ = v_reuseFailAlloc_7034_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7033_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2___boxed(
    mut v_as_7038_: *mut LeanObject,
    mut v_sz_7039_: *mut LeanObject,
    mut v_i_7040_: *mut LeanObject,
    mut v_b_7041_: *mut LeanObject,
    mut v___y_7042_: *mut LeanObject,
    mut v___y_7043_: *mut LeanObject,
    mut v___y_7044_: *mut LeanObject,
    mut v___y_7045_: *mut LeanObject,
    mut v___y_7046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7047_: usize = 0;
    let mut v_i_boxed_7048_: usize = 0;
    let mut v_res_7049_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7047_ = lean_unbox_usize(v_sz_7039_);
    lean_dec(v_sz_7039_);
    v_i_boxed_7048_ = lean_unbox_usize(v_i_7040_);
    lean_dec(v_i_7040_);
    v_res_7049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_as_7038_, v_sz_boxed_7047_, v_i_boxed_7048_, v_b_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
    lean_dec(v___y_7045_);
    lean_dec_ref(v___y_7044_);
    lean_dec(v___y_7043_);
    lean_dec_ref(v___y_7042_);
    lean_dec_ref(v_as_7038_);
    return v_res_7049_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(
    mut v_init_7050_: *mut LeanObject,
    mut v_n_7051_: *mut LeanObject,
    mut v_b_7052_: *mut LeanObject,
    mut v___y_7053_: *mut LeanObject,
    mut v___y_7054_: *mut LeanObject,
    mut v___y_7055_: *mut LeanObject,
    mut v___y_7056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_7058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7061_: usize = 0;
    let mut v___x_7062_: usize = 0;
    let mut v___x_7063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7067_: u8 = 0;
    let mut v_fst_7068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7078_: u8 = 0;
    let mut v_a_7079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7082_: u8 = 0;
    let mut v___x_7084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7086_: u8 = 0;
    let mut v_vs_7087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7090_: usize = 0;
    let mut v___x_7091_: usize = 0;
    let mut v___x_7092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7096_: u8 = 0;
    let mut v_fst_7097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7107_: u8 = 0;
    let mut v_a_7108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7111_: u8 = 0;
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7115_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_7051_) == 0 {
                    v_cs_7058_ = lean_ctor_get(v_n_7051_, 0);
                    v___x_7059_ = lean_box(0);
                    v___x_7060_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7060_, 0, v___x_7059_);
                    lean_ctor_set(v___x_7060_, 1, v_b_7052_);
                    v_sz_7061_ = lean_array_size(v_cs_7058_);
                    v___x_7062_ = 0usize;
                    v___x_7063_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_7050_, v_cs_7058_, v_sz_7061_, v___x_7062_, v___x_7060_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
                    if lean_obj_tag(v___x_7063_) == 0 {
                        v_a_7064_ = lean_ctor_get(v___x_7063_, 0);
                        v_isSharedCheck_7078_ = (!lean_is_exclusive(v___x_7063_)) as u8;
                        if v_isSharedCheck_7078_ == 0 {
                            v___x_7066_ = v___x_7063_;
                            v_isShared_7067_ = v_isSharedCheck_7078_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7064_);
                            lean_dec(v___x_7063_);
                            v___x_7066_ = lean_box(0);
                            v_isShared_7067_ = v_isSharedCheck_7078_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_7079_ = lean_ctor_get(v___x_7063_, 0);
                        v_isSharedCheck_7086_ = (!lean_is_exclusive(v___x_7063_)) as u8;
                        if v_isSharedCheck_7086_ == 0 {
                            v___x_7081_ = v___x_7063_;
                            v_isShared_7082_ = v_isSharedCheck_7086_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_7079_);
                            lean_dec(v___x_7063_);
                            v___x_7081_ = lean_box(0);
                            v_isShared_7082_ = v_isSharedCheck_7086_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_7087_ = lean_ctor_get(v_n_7051_, 0);
                    v___x_7088_ = lean_box(0);
                    v___x_7089_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7089_, 0, v___x_7088_);
                    lean_ctor_set(v___x_7089_, 1, v_b_7052_);
                    v_sz_7090_ = lean_array_size(v_vs_7087_);
                    v___x_7091_ = 0usize;
                    v___x_7092_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__2(v_vs_7087_, v_sz_7090_, v___x_7091_, v___x_7089_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
                    if lean_obj_tag(v___x_7092_) == 0 {
                        v_a_7093_ = lean_ctor_get(v___x_7092_, 0);
                        v_isSharedCheck_7107_ = (!lean_is_exclusive(v___x_7092_)) as u8;
                        if v_isSharedCheck_7107_ == 0 {
                            v___x_7095_ = v___x_7092_;
                            v_isShared_7096_ = v_isSharedCheck_7107_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7093_);
                            lean_dec(v___x_7092_);
                            v___x_7095_ = lean_box(0);
                            v_isShared_7096_ = v_isSharedCheck_7107_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_7108_ = lean_ctor_get(v___x_7092_, 0);
                        v_isSharedCheck_7115_ = (!lean_is_exclusive(v___x_7092_)) as u8;
                        if v_isSharedCheck_7115_ == 0 {
                            v___x_7110_ = v___x_7092_;
                            v_isShared_7111_ = v_isSharedCheck_7115_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_7108_);
                            lean_dec(v___x_7092_);
                            v___x_7110_ = lean_box(0);
                            v_isShared_7111_ = v_isSharedCheck_7115_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_7068_ = lean_ctor_get(v_a_7064_, 0);
                if lean_obj_tag(v_fst_7068_) == 0 {
                    v_snd_7069_ = lean_ctor_get(v_a_7064_, 1);
                    lean_inc(v_snd_7069_);
                    lean_dec(v_a_7064_);
                    v___x_7070_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7070_, 0, v_snd_7069_);
                    if v_isShared_7067_ == 0 {
                        lean_ctor_set(v___x_7066_, 0, v___x_7070_);
                        v___x_7072_ = v___x_7066_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7073_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7073_, 0, v___x_7070_);
                        v___x_7072_ = v_reuseFailAlloc_7073_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7068_);
                    lean_dec(v_a_7064_);
                    v_val_7074_ = lean_ctor_get(v_fst_7068_, 0);
                    lean_inc(v_val_7074_);
                    lean_dec_ref_known(v_fst_7068_, 1);
                    if v_isShared_7067_ == 0 {
                        lean_ctor_set(v___x_7066_, 0, v_val_7074_);
                        v___x_7076_ = v___x_7066_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7077_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7077_, 0, v_val_7074_);
                        v___x_7076_ = v_reuseFailAlloc_7077_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7072_;
            }
            3 => {
                return v___x_7076_;
            }
            4 => {
                if v_isShared_7082_ == 0 {
                    v___x_7084_ = v___x_7081_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7085_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7085_, 0, v_a_7079_);
                    v___x_7084_ = v_reuseFailAlloc_7085_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7084_;
            }
            6 => {
                v_fst_7097_ = lean_ctor_get(v_a_7093_, 0);
                if lean_obj_tag(v_fst_7097_) == 0 {
                    v_snd_7098_ = lean_ctor_get(v_a_7093_, 1);
                    lean_inc(v_snd_7098_);
                    lean_dec(v_a_7093_);
                    v___x_7099_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7099_, 0, v_snd_7098_);
                    if v_isShared_7096_ == 0 {
                        lean_ctor_set(v___x_7095_, 0, v___x_7099_);
                        v___x_7101_ = v___x_7095_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_7102_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7102_, 0, v___x_7099_);
                        v___x_7101_ = v_reuseFailAlloc_7102_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7097_);
                    lean_dec(v_a_7093_);
                    v_val_7103_ = lean_ctor_get(v_fst_7097_, 0);
                    lean_inc(v_val_7103_);
                    lean_dec_ref_known(v_fst_7097_, 1);
                    if v_isShared_7096_ == 0 {
                        lean_ctor_set(v___x_7095_, 0, v_val_7103_);
                        v___x_7105_ = v___x_7095_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_7106_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7106_, 0, v_val_7103_);
                        v___x_7105_ = v_reuseFailAlloc_7106_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_7101_;
            }
            8 => {
                return v___x_7105_;
            }
            9 => {
                if v_isShared_7111_ == 0 {
                    v___x_7113_ = v___x_7110_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7114_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7114_, 0, v_a_7108_);
                    v___x_7113_ = v_reuseFailAlloc_7114_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_7113_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(
    mut v_init_7116_: *mut LeanObject,
    mut v_as_7117_: *mut LeanObject,
    mut v_sz_7118_: usize,
    mut v_i_7119_: usize,
    mut v_b_7120_: *mut LeanObject,
    mut v___y_7121_: *mut LeanObject,
    mut v___y_7122_: *mut LeanObject,
    mut v___y_7123_: *mut LeanObject,
    mut v___y_7124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7126_: u8 = 0;
    let mut v___x_7127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7131_: u8 = 0;
    let mut v_a_7132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7137_: u8 = 0;
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7149_: usize = 0;
    let mut v___x_7150_: usize = 0;
    let mut v_reuseFailAlloc_7152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7153_: u8 = 0;
    let mut v_a_7154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7157_: u8 = 0;
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7161_: u8 = 0;
    let mut v_isSharedCheck_7162_: u8 = 0;
    let mut v_unused_7163_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7126_ = lean_usize_dec_lt(v_i_7119_, v_sz_7118_);
                if v___x_7126_ == 0 {
                    v___x_7127_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7127_, 0, v_b_7120_);
                    return v___x_7127_;
                } else {
                    v_snd_7128_ = lean_ctor_get(v_b_7120_, 1);
                    v_isSharedCheck_7162_ = (!lean_is_exclusive(v_b_7120_)) as u8;
                    if v_isSharedCheck_7162_ == 0 {
                        v_unused_7163_ = lean_ctor_get(v_b_7120_, 0);
                        lean_dec(v_unused_7163_);
                        v___x_7130_ = v_b_7120_;
                        v_isShared_7131_ = v_isSharedCheck_7162_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7128_);
                        lean_dec(v_b_7120_);
                        v___x_7130_ = lean_box(0);
                        v_isShared_7131_ = v_isSharedCheck_7162_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_7132_ = lean_array_uget_borrowed(v_as_7117_, v_i_7119_);
                lean_inc(v_snd_7128_);
                v___x_7133_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_7116_, v_a_7132_, v_snd_7128_, v___y_7121_, v___y_7122_, v___y_7123_, v___y_7124_);
                if lean_obj_tag(v___x_7133_) == 0 {
                    v_a_7134_ = lean_ctor_get(v___x_7133_, 0);
                    v_isSharedCheck_7153_ = (!lean_is_exclusive(v___x_7133_)) as u8;
                    if v_isSharedCheck_7153_ == 0 {
                        v___x_7136_ = v___x_7133_;
                        v_isShared_7137_ = v_isSharedCheck_7153_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_7134_);
                        lean_dec(v___x_7133_);
                        v___x_7136_ = lean_box(0);
                        v_isShared_7137_ = v_isSharedCheck_7153_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7130_);
                    lean_dec(v_snd_7128_);
                    v_a_7154_ = lean_ctor_get(v___x_7133_, 0);
                    v_isSharedCheck_7161_ = (!lean_is_exclusive(v___x_7133_)) as u8;
                    if v_isSharedCheck_7161_ == 0 {
                        v___x_7156_ = v___x_7133_;
                        v_isShared_7157_ = v_isSharedCheck_7161_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_7154_);
                        lean_dec(v___x_7133_);
                        v___x_7156_ = lean_box(0);
                        v_isShared_7157_ = v_isSharedCheck_7161_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_7134_) == 0 {
                    v___x_7138_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7138_, 0, v_a_7134_);
                    if v_isShared_7131_ == 0 {
                        lean_ctor_set(v___x_7130_, 0, v___x_7138_);
                        v___x_7140_ = v___x_7130_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_7144_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7144_, 0, v___x_7138_);
                        lean_ctor_set(v_reuseFailAlloc_7144_, 1, v_snd_7128_);
                        v___x_7140_ = v_reuseFailAlloc_7144_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7136_);
                    lean_dec(v_snd_7128_);
                    v_a_7145_ = lean_ctor_get(v_a_7134_, 0);
                    lean_inc(v_a_7145_);
                    lean_dec_ref_known(v_a_7134_, 1);
                    v___x_7146_ = lean_box(0);
                    if v_isShared_7131_ == 0 {
                        lean_ctor_set(v___x_7130_, 1, v_a_7145_);
                        lean_ctor_set(v___x_7130_, 0, v___x_7146_);
                        v___x_7148_ = v___x_7130_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7152_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7152_, 0, v___x_7146_);
                        lean_ctor_set(v_reuseFailAlloc_7152_, 1, v_a_7145_);
                        v___x_7148_ = v_reuseFailAlloc_7152_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7137_ == 0 {
                    lean_ctor_set(v___x_7136_, 0, v___x_7140_);
                    v___x_7142_ = v___x_7136_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7143_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7143_, 0, v___x_7140_);
                    v___x_7142_ = v_reuseFailAlloc_7143_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7142_;
            }
            5 => {
                v___x_7149_ = 1usize;
                v___x_7150_ = lean_usize_add(v_i_7119_, v___x_7149_);
                v_i_7119_ = v___x_7150_;
                v_b_7120_ = v___x_7148_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_7157_ == 0 {
                    v___x_7159_ = v___x_7156_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7160_, 0, v_a_7154_);
                    v___x_7159_ = v_reuseFailAlloc_7160_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7159_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1___boxed(
    mut v_init_7164_: *mut LeanObject,
    mut v_as_7165_: *mut LeanObject,
    mut v_sz_7166_: *mut LeanObject,
    mut v_i_7167_: *mut LeanObject,
    mut v_b_7168_: *mut LeanObject,
    mut v___y_7169_: *mut LeanObject,
    mut v___y_7170_: *mut LeanObject,
    mut v___y_7171_: *mut LeanObject,
    mut v___y_7172_: *mut LeanObject,
    mut v___y_7173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7174_: usize = 0;
    let mut v_i_boxed_7175_: usize = 0;
    let mut v_res_7176_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7174_ = lean_unbox_usize(v_sz_7166_);
    lean_dec(v_sz_7166_);
    v_i_boxed_7175_ = lean_unbox_usize(v_i_7167_);
    lean_dec(v_i_7167_);
    v_res_7176_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0_spec__1(v_init_7164_, v_as_7165_, v_sz_boxed_7174_, v_i_boxed_7175_, v_b_7168_, v___y_7169_, v___y_7170_, v___y_7171_, v___y_7172_);
    lean_dec(v___y_7172_);
    lean_dec_ref(v___y_7171_);
    lean_dec(v___y_7170_);
    lean_dec_ref(v___y_7169_);
    lean_dec_ref(v_as_7165_);
    lean_dec_ref(v_init_7164_);
    return v_res_7176_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0___boxed(
    mut v_init_7177_: *mut LeanObject,
    mut v_n_7178_: *mut LeanObject,
    mut v_b_7179_: *mut LeanObject,
    mut v___y_7180_: *mut LeanObject,
    mut v___y_7181_: *mut LeanObject,
    mut v___y_7182_: *mut LeanObject,
    mut v___y_7183_: *mut LeanObject,
    mut v___y_7184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7185_: *mut LeanObject = core::ptr::null_mut();
    v_res_7185_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_7177_, v_n_7178_, v_b_7179_, v___y_7180_, v___y_7181_, v___y_7182_, v___y_7183_);
    lean_dec(v___y_7183_);
    lean_dec_ref(v___y_7182_);
    lean_dec(v___y_7181_);
    lean_dec_ref(v___y_7180_);
    lean_dec_ref(v_n_7178_);
    lean_dec_ref(v_init_7177_);
    return v_res_7185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(
    mut v_as_7186_: *mut LeanObject,
    mut v_sz_7187_: usize,
    mut v_i_7188_: usize,
    mut v_b_7189_: *mut LeanObject,
    mut v___y_7190_: *mut LeanObject,
    mut v___y_7191_: *mut LeanObject,
    mut v___y_7192_: *mut LeanObject,
    mut v___y_7193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7195_: u8 = 0;
    let mut v___x_7196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7200_: u8 = 0;
    let mut v___x_7201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7206_: usize = 0;
    let mut v___x_7207_: usize = 0;
    let mut v_reuseFailAlloc_7209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7212_: u8 = 0;
    let mut v___x_7213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: u8 = 0;
    let mut v___x_7217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7222_: u8 = 0;
    let mut v___x_7224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7226_: u8 = 0;
    let mut v_isSharedCheck_7227_: u8 = 0;
    let mut v_unused_7228_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7195_ = lean_usize_dec_lt(v_i_7188_, v_sz_7187_);
                if v___x_7195_ == 0 {
                    v___x_7196_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7196_, 0, v_b_7189_);
                    return v___x_7196_;
                } else {
                    v_snd_7197_ = lean_ctor_get(v_b_7189_, 1);
                    v_isSharedCheck_7227_ = (!lean_is_exclusive(v_b_7189_)) as u8;
                    if v_isSharedCheck_7227_ == 0 {
                        v_unused_7228_ = lean_ctor_get(v_b_7189_, 0);
                        lean_dec(v_unused_7228_);
                        v___x_7199_ = v_b_7189_;
                        v_isShared_7200_ = v_isSharedCheck_7227_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7197_);
                        lean_dec(v_b_7189_);
                        v___x_7199_ = lean_box(0);
                        v_isShared_7200_ = v_isSharedCheck_7227_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7201_ = lean_box(0);
                v_a_7210_ = lean_array_uget_borrowed(v_as_7186_, v_i_7188_);
                if lean_obj_tag(v_a_7210_) == 0 {
                    v_a_7203_ = v_snd_7197_;
                    state = 2;
                    continue;
                } else {
                    v_val_7211_ = lean_ctor_get(v_a_7210_, 0);
                    v___x_7212_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7211_);
                    if v___x_7212_ == 0 {
                        v___x_7213_ = l_Lean_LocalDecl_type(v_val_7211_);
                        v___x_7214_ = l_Lean_Meta_isProp(
                            v___x_7213_,
                            v___y_7190_,
                            v___y_7191_,
                            v___y_7192_,
                            v___y_7193_,
                        );
                        if lean_obj_tag(v___x_7214_) == 0 {
                            v_a_7215_ = lean_ctor_get(v___x_7214_, 0);
                            lean_inc(v_a_7215_);
                            lean_dec_ref_known(v___x_7214_, 1);
                            v___x_7216_ = (lean_unbox(v_a_7215_) as u8);
                            lean_dec(v_a_7215_);
                            if v___x_7216_ == 0 {
                                v_a_7203_ = v_snd_7197_;
                                state = 2;
                                continue;
                            } else {
                                v___x_7217_ = l_Lean_LocalDecl_fvarId(v_val_7211_);
                                v___x_7218_ = lean_array_push(v_snd_7197_, v___x_7217_);
                                v_a_7203_ = v___x_7218_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7199_);
                            lean_dec(v_snd_7197_);
                            v_a_7219_ = lean_ctor_get(v___x_7214_, 0);
                            v_isSharedCheck_7226_ = (!lean_is_exclusive(v___x_7214_)) as u8;
                            if v_isSharedCheck_7226_ == 0 {
                                v___x_7221_ = v___x_7214_;
                                v_isShared_7222_ = v_isSharedCheck_7226_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_7219_);
                                lean_dec(v___x_7214_);
                                v___x_7221_ = lean_box(0);
                                v_isShared_7222_ = v_isSharedCheck_7226_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_7203_ = v_snd_7197_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7200_ == 0 {
                    lean_ctor_set(v___x_7199_, 1, v_a_7203_);
                    lean_ctor_set(v___x_7199_, 0, v___x_7201_);
                    v___x_7205_ = v___x_7199_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7209_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7209_, 0, v___x_7201_);
                    lean_ctor_set(v_reuseFailAlloc_7209_, 1, v_a_7203_);
                    v___x_7205_ = v_reuseFailAlloc_7209_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7206_ = 1usize;
                v___x_7207_ = lean_usize_add(v_i_7188_, v___x_7206_);
                v_i_7188_ = v___x_7207_;
                v_b_7189_ = v___x_7205_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_7222_ == 0 {
                    v___x_7224_ = v___x_7221_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7225_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7225_, 0, v_a_7219_);
                    v___x_7224_ = v_reuseFailAlloc_7225_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7224_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4___boxed(
    mut v_as_7229_: *mut LeanObject,
    mut v_sz_7230_: *mut LeanObject,
    mut v_i_7231_: *mut LeanObject,
    mut v_b_7232_: *mut LeanObject,
    mut v___y_7233_: *mut LeanObject,
    mut v___y_7234_: *mut LeanObject,
    mut v___y_7235_: *mut LeanObject,
    mut v___y_7236_: *mut LeanObject,
    mut v___y_7237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7238_: usize = 0;
    let mut v_i_boxed_7239_: usize = 0;
    let mut v_res_7240_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7238_ = lean_unbox_usize(v_sz_7230_);
    lean_dec(v_sz_7230_);
    v_i_boxed_7239_ = lean_unbox_usize(v_i_7231_);
    lean_dec(v_i_7231_);
    v_res_7240_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_7229_, v_sz_boxed_7238_, v_i_boxed_7239_, v_b_7232_, v___y_7233_, v___y_7234_, v___y_7235_, v___y_7236_);
    lean_dec(v___y_7236_);
    lean_dec_ref(v___y_7235_);
    lean_dec(v___y_7234_);
    lean_dec_ref(v___y_7233_);
    lean_dec_ref(v_as_7229_);
    return v_res_7240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(
    mut v_as_7241_: *mut LeanObject,
    mut v_sz_7242_: usize,
    mut v_i_7243_: usize,
    mut v_b_7244_: *mut LeanObject,
    mut v___y_7245_: *mut LeanObject,
    mut v___y_7246_: *mut LeanObject,
    mut v___y_7247_: *mut LeanObject,
    mut v___y_7248_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7250_: u8 = 0;
    let mut v___x_7251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7255_: u8 = 0;
    let mut v___x_7256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: usize = 0;
    let mut v___x_7262_: usize = 0;
    let mut v___x_7263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7267_: u8 = 0;
    let mut v___x_7268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: u8 = 0;
    let mut v___x_7272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7277_: u8 = 0;
    let mut v___x_7279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7281_: u8 = 0;
    let mut v_isSharedCheck_7282_: u8 = 0;
    let mut v_unused_7283_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7250_ = lean_usize_dec_lt(v_i_7243_, v_sz_7242_);
                if v___x_7250_ == 0 {
                    v___x_7251_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7251_, 0, v_b_7244_);
                    return v___x_7251_;
                } else {
                    v_snd_7252_ = lean_ctor_get(v_b_7244_, 1);
                    v_isSharedCheck_7282_ = (!lean_is_exclusive(v_b_7244_)) as u8;
                    if v_isSharedCheck_7282_ == 0 {
                        v_unused_7283_ = lean_ctor_get(v_b_7244_, 0);
                        lean_dec(v_unused_7283_);
                        v___x_7254_ = v_b_7244_;
                        v_isShared_7255_ = v_isSharedCheck_7282_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_7252_);
                        lean_dec(v_b_7244_);
                        v___x_7254_ = lean_box(0);
                        v_isShared_7255_ = v_isSharedCheck_7282_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7256_ = lean_box(0);
                v_a_7265_ = lean_array_uget_borrowed(v_as_7241_, v_i_7243_);
                if lean_obj_tag(v_a_7265_) == 0 {
                    v_a_7258_ = v_snd_7252_;
                    state = 2;
                    continue;
                } else {
                    v_val_7266_ = lean_ctor_get(v_a_7265_, 0);
                    v___x_7267_ = l_Lean_LocalDecl_isImplementationDetail(v_val_7266_);
                    if v___x_7267_ == 0 {
                        v___x_7268_ = l_Lean_LocalDecl_type(v_val_7266_);
                        v___x_7269_ = l_Lean_Meta_isProp(
                            v___x_7268_,
                            v___y_7245_,
                            v___y_7246_,
                            v___y_7247_,
                            v___y_7248_,
                        );
                        if lean_obj_tag(v___x_7269_) == 0 {
                            v_a_7270_ = lean_ctor_get(v___x_7269_, 0);
                            lean_inc(v_a_7270_);
                            lean_dec_ref_known(v___x_7269_, 1);
                            v___x_7271_ = (lean_unbox(v_a_7270_) as u8);
                            lean_dec(v_a_7270_);
                            if v___x_7271_ == 0 {
                                v_a_7258_ = v_snd_7252_;
                                state = 2;
                                continue;
                            } else {
                                v___x_7272_ = l_Lean_LocalDecl_fvarId(v_val_7266_);
                                v___x_7273_ = lean_array_push(v_snd_7252_, v___x_7272_);
                                v_a_7258_ = v___x_7273_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_7254_);
                            lean_dec(v_snd_7252_);
                            v_a_7274_ = lean_ctor_get(v___x_7269_, 0);
                            v_isSharedCheck_7281_ = (!lean_is_exclusive(v___x_7269_)) as u8;
                            if v_isSharedCheck_7281_ == 0 {
                                v___x_7276_ = v___x_7269_;
                                v_isShared_7277_ = v_isSharedCheck_7281_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_7274_);
                                lean_dec(v___x_7269_);
                                v___x_7276_ = lean_box(0);
                                v_isShared_7277_ = v_isSharedCheck_7281_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_7258_ = v_snd_7252_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_7255_ == 0 {
                    lean_ctor_set(v___x_7254_, 1, v_a_7258_);
                    lean_ctor_set(v___x_7254_, 0, v___x_7256_);
                    v___x_7260_ = v___x_7254_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7264_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7264_, 0, v___x_7256_);
                    lean_ctor_set(v_reuseFailAlloc_7264_, 1, v_a_7258_);
                    v___x_7260_ = v_reuseFailAlloc_7264_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7261_ = 1usize;
                v___x_7262_ = lean_usize_add(v_i_7243_, v___x_7261_);
                v___x_7263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1_spec__4(v_as_7241_, v_sz_7242_, v___x_7262_, v___x_7260_, v___y_7245_, v___y_7246_, v___y_7247_, v___y_7248_);
                return v___x_7263_;
            }
            4 => {
                if v_isShared_7277_ == 0 {
                    v___x_7279_ = v___x_7276_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7280_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7280_, 0, v_a_7274_);
                    v___x_7279_ = v_reuseFailAlloc_7280_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1___boxed(
    mut v_as_7284_: *mut LeanObject,
    mut v_sz_7285_: *mut LeanObject,
    mut v_i_7286_: *mut LeanObject,
    mut v_b_7287_: *mut LeanObject,
    mut v___y_7288_: *mut LeanObject,
    mut v___y_7289_: *mut LeanObject,
    mut v___y_7290_: *mut LeanObject,
    mut v___y_7291_: *mut LeanObject,
    mut v___y_7292_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7293_: usize = 0;
    let mut v_i_boxed_7294_: usize = 0;
    let mut v_res_7295_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7293_ = lean_unbox_usize(v_sz_7285_);
    lean_dec(v_sz_7285_);
    v_i_boxed_7294_ = lean_unbox_usize(v_i_7286_);
    lean_dec(v_i_7286_);
    v_res_7295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_as_7284_, v_sz_boxed_7293_, v_i_boxed_7294_, v_b_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_);
    lean_dec(v___y_7291_);
    lean_dec_ref(v___y_7290_);
    lean_dec(v___y_7289_);
    lean_dec_ref(v___y_7288_);
    lean_dec_ref(v_as_7284_);
    return v_res_7295_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(
    mut v_t_7296_: *mut LeanObject,
    mut v_init_7297_: *mut LeanObject,
    mut v___y_7298_: *mut LeanObject,
    mut v___y_7299_: *mut LeanObject,
    mut v___y_7300_: *mut LeanObject,
    mut v___y_7301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_7303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_7304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7309_: u8 = 0;
    let mut v_a_7310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_7317_: usize = 0;
    let mut v___x_7318_: usize = 0;
    let mut v___x_7319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7323_: u8 = 0;
    let mut v_fst_7324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_7325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_7329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7333_: u8 = 0;
    let mut v_a_7334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7337_: u8 = 0;
    let mut v___x_7339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7341_: u8 = 0;
    let mut v_isSharedCheck_7342_: u8 = 0;
    let mut v_a_7343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7346_: u8 = 0;
    let mut v___x_7348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_7303_ = lean_ctor_get(v_t_7296_, 0);
                v_tail_7304_ = lean_ctor_get(v_t_7296_, 1);
                lean_inc_ref(v_init_7297_);
                v___x_7305_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__0(v_init_7297_, v_root_7303_, v_init_7297_, v___y_7298_, v___y_7299_, v___y_7300_, v___y_7301_);
                lean_dec_ref(v_init_7297_);
                if lean_obj_tag(v___x_7305_) == 0 {
                    v_a_7306_ = lean_ctor_get(v___x_7305_, 0);
                    v_isSharedCheck_7342_ = (!lean_is_exclusive(v___x_7305_)) as u8;
                    if v_isSharedCheck_7342_ == 0 {
                        v___x_7308_ = v___x_7305_;
                        v_isShared_7309_ = v_isSharedCheck_7342_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_7306_);
                        lean_dec(v___x_7305_);
                        v___x_7308_ = lean_box(0);
                        v_isShared_7309_ = v_isSharedCheck_7342_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7343_ = lean_ctor_get(v___x_7305_, 0);
                    v_isSharedCheck_7350_ = (!lean_is_exclusive(v___x_7305_)) as u8;
                    if v_isSharedCheck_7350_ == 0 {
                        v___x_7345_ = v___x_7305_;
                        v_isShared_7346_ = v_isSharedCheck_7350_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_7343_);
                        lean_dec(v___x_7305_);
                        v___x_7345_ = lean_box(0);
                        v_isShared_7346_ = v_isSharedCheck_7350_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_7306_) == 0 {
                    v_a_7310_ = lean_ctor_get(v_a_7306_, 0);
                    lean_inc(v_a_7310_);
                    lean_dec_ref_known(v_a_7306_, 1);
                    if v_isShared_7309_ == 0 {
                        lean_ctor_set(v___x_7308_, 0, v_a_7310_);
                        v___x_7312_ = v___x_7308_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7313_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7313_, 0, v_a_7310_);
                        v___x_7312_ = v_reuseFailAlloc_7313_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_7308_);
                    v_a_7314_ = lean_ctor_get(v_a_7306_, 0);
                    lean_inc(v_a_7314_);
                    lean_dec_ref_known(v_a_7306_, 1);
                    v___x_7315_ = lean_box(0);
                    v___x_7316_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_7316_, 0, v___x_7315_);
                    lean_ctor_set(v___x_7316_, 1, v_a_7314_);
                    v_sz_7317_ = lean_array_size(v_tail_7304_);
                    v___x_7318_ = 0usize;
                    v___x_7319_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0_spec__1(v_tail_7304_, v_sz_7317_, v___x_7318_, v___x_7316_, v___y_7298_, v___y_7299_, v___y_7300_, v___y_7301_);
                    if lean_obj_tag(v___x_7319_) == 0 {
                        v_a_7320_ = lean_ctor_get(v___x_7319_, 0);
                        v_isSharedCheck_7333_ = (!lean_is_exclusive(v___x_7319_)) as u8;
                        if v_isSharedCheck_7333_ == 0 {
                            v___x_7322_ = v___x_7319_;
                            v_isShared_7323_ = v_isSharedCheck_7333_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7320_);
                            lean_dec(v___x_7319_);
                            v___x_7322_ = lean_box(0);
                            v_isShared_7323_ = v_isSharedCheck_7333_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_7334_ = lean_ctor_get(v___x_7319_, 0);
                        v_isSharedCheck_7341_ = (!lean_is_exclusive(v___x_7319_)) as u8;
                        if v_isSharedCheck_7341_ == 0 {
                            v___x_7336_ = v___x_7319_;
                            v_isShared_7337_ = v_isSharedCheck_7341_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_7334_);
                            lean_dec(v___x_7319_);
                            v___x_7336_ = lean_box(0);
                            v_isShared_7337_ = v_isSharedCheck_7341_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_7312_;
            }
            3 => {
                v_fst_7324_ = lean_ctor_get(v_a_7320_, 0);
                if lean_obj_tag(v_fst_7324_) == 0 {
                    v_snd_7325_ = lean_ctor_get(v_a_7320_, 1);
                    lean_inc(v_snd_7325_);
                    lean_dec(v_a_7320_);
                    if v_isShared_7323_ == 0 {
                        lean_ctor_set(v___x_7322_, 0, v_snd_7325_);
                        v___x_7327_ = v___x_7322_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7328_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7328_, 0, v_snd_7325_);
                        v___x_7327_ = v_reuseFailAlloc_7328_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_7324_);
                    lean_dec(v_a_7320_);
                    v_val_7329_ = lean_ctor_get(v_fst_7324_, 0);
                    lean_inc(v_val_7329_);
                    lean_dec_ref_known(v_fst_7324_, 1);
                    if v_isShared_7323_ == 0 {
                        lean_ctor_set(v___x_7322_, 0, v_val_7329_);
                        v___x_7331_ = v___x_7322_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7332_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7332_, 0, v_val_7329_);
                        v___x_7331_ = v_reuseFailAlloc_7332_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7327_;
            }
            5 => {
                return v___x_7331_;
            }
            6 => {
                if v_isShared_7337_ == 0 {
                    v___x_7339_ = v___x_7336_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7340_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7340_, 0, v_a_7334_);
                    v___x_7339_ = v_reuseFailAlloc_7340_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7339_;
            }
            8 => {
                if v_isShared_7346_ == 0 {
                    v___x_7348_ = v___x_7345_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7349_, 0, v_a_7343_);
                    v___x_7348_ = v_reuseFailAlloc_7349_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0___boxed(
    mut v_t_7351_: *mut LeanObject,
    mut v_init_7352_: *mut LeanObject,
    mut v___y_7353_: *mut LeanObject,
    mut v___y_7354_: *mut LeanObject,
    mut v___y_7355_: *mut LeanObject,
    mut v___y_7356_: *mut LeanObject,
    mut v___y_7357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7358_: *mut LeanObject = core::ptr::null_mut();
    v_res_7358_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(
        v_t_7351_,
        v_init_7352_,
        v___y_7353_,
        v___y_7354_,
        v___y_7355_,
        v___y_7356_,
    );
    lean_dec(v___y_7356_);
    lean_dec_ref(v___y_7355_);
    lean_dec(v___y_7354_);
    lean_dec_ref(v___y_7353_);
    lean_dec_ref(v_t_7351_);
    return v_res_7358_;
}
pub unsafe fn l_Lean_Meta_getPropHyps(
    mut v_a_7359_: *mut LeanObject,
    mut v_a_7360_: *mut LeanObject,
    mut v_a_7361_: *mut LeanObject,
    mut v_a_7362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lctx_7364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_7365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_result_7366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7367_: *mut LeanObject = core::ptr::null_mut();
    v_lctx_7364_ = lean_ctor_get(v_a_7359_, 2);
    v_decls_7365_ = lean_ctor_get(v_lctx_7364_, 1);
    v_result_7366_ = l_Lean_MVarId_getNondepPropHyps___lam__2___closed__0;
    v___x_7367_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getPropHyps_spec__0(
        v_decls_7365_,
        v_result_7366_,
        v_a_7359_,
        v_a_7360_,
        v_a_7361_,
        v_a_7362_,
    );
    return v___x_7367_;
}
pub unsafe fn l_Lean_Meta_getPropHyps___boxed(
    mut v_a_7368_: *mut LeanObject,
    mut v_a_7369_: *mut LeanObject,
    mut v_a_7370_: *mut LeanObject,
    mut v_a_7371_: *mut LeanObject,
    mut v_a_7372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7373_: *mut LeanObject = core::ptr::null_mut();
    v_res_7373_ = l_Lean_Meta_getPropHyps(v_a_7368_, v_a_7369_, v_a_7370_, v_a_7371_);
    lean_dec(v_a_7371_);
    lean_dec_ref(v_a_7370_);
    lean_dec(v_a_7369_);
    lean_dec_ref(v_a_7368_);
    return v_res_7373_;
}
pub unsafe fn _init_l_Lean_MVarId_inferInstance___lam__0___closed__2() -> *mut LeanObject {
    let mut v___x_7377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7378_: *mut LeanObject = core::ptr::null_mut();
    v___x_7377_ = l_Lean_MVarId_inferInstance___lam__0___closed__1;
    v___x_7378_ = l_Lean_MessageData_ofFormat(v___x_7377_);
    return v___x_7378_;
}
pub unsafe fn _init_l_Lean_MVarId_inferInstance___lam__0___closed__3() -> *mut LeanObject {
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7380_: *mut LeanObject = core::ptr::null_mut();
    v___x_7379_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_MVarId_inferInstance___lam__0___closed__2),
        core::ptr::addr_of_mut!(l_Lean_MVarId_inferInstance___lam__0___closed__2_once),
        _init_l_Lean_MVarId_inferInstance___lam__0___closed__2,
    );
    v___x_7380_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_7380_, 0, v___x_7379_);
    return v___x_7380_;
}
pub unsafe fn l_Lean_MVarId_inferInstance___lam__0(
    mut v_mvarId_7381_: *mut LeanObject,
    mut v___x_7382_: *mut LeanObject,
    mut v___y_7383_: *mut LeanObject,
    mut v___y_7384_: *mut LeanObject,
    mut v___y_7385_: *mut LeanObject,
    mut v___y_7386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7399_: u8 = 0;
    let mut v___x_7400_: u8 = 0;
    let mut v___x_7401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7407_: u8 = 0;
    let mut v_a_7408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7411_: u8 = 0;
    let mut v___x_7413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7415_: u8 = 0;
    let mut v_a_7416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7419_: u8 = 0;
    let mut v___x_7421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7423_: u8 = 0;
    let mut v_a_7424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7427_: u8 = 0;
    let mut v___x_7429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___x_7382_);
                lean_inc(v_mvarId_7381_);
                v___x_7388_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_7381_,
                    v___x_7382_,
                    v___y_7383_,
                    v___y_7384_,
                    v___y_7385_,
                    v___y_7386_,
                );
                if lean_obj_tag(v___x_7388_) == 0 {
                    lean_dec_ref_known(v___x_7388_, 1);
                    lean_inc(v_mvarId_7381_);
                    v___x_7389_ = l_Lean_MVarId_getType(
                        v_mvarId_7381_,
                        v___y_7383_,
                        v___y_7384_,
                        v___y_7385_,
                        v___y_7386_,
                    );
                    if lean_obj_tag(v___x_7389_) == 0 {
                        v_a_7390_ = lean_ctor_get(v___x_7389_, 0);
                        lean_inc(v_a_7390_);
                        lean_dec_ref_known(v___x_7389_, 1);
                        v___x_7391_ = lean_box(0);
                        v___x_7392_ = l_Lean_Meta_synthInstance(
                            v_a_7390_,
                            v___x_7391_,
                            v___y_7383_,
                            v___y_7384_,
                            v___y_7385_,
                            v___y_7386_,
                        );
                        if lean_obj_tag(v___x_7392_) == 0 {
                            v_a_7393_ = lean_ctor_get(v___x_7392_, 0);
                            lean_inc(v_a_7393_);
                            lean_dec_ref_known(v___x_7392_, 1);
                            lean_inc(v_mvarId_7381_);
                            v___x_7394_ = l_Lean_mkMVar(v_mvarId_7381_);
                            v___x_7395_ = l_Lean_Meta_isExprDefEq(
                                v___x_7394_,
                                v_a_7393_,
                                v___y_7383_,
                                v___y_7384_,
                                v___y_7385_,
                                v___y_7386_,
                            );
                            if lean_obj_tag(v___x_7395_) == 0 {
                                v_a_7396_ = lean_ctor_get(v___x_7395_, 0);
                                v_isSharedCheck_7407_ = (!lean_is_exclusive(v___x_7395_)) as u8;
                                if v_isSharedCheck_7407_ == 0 {
                                    v___x_7398_ = v___x_7395_;
                                    v_isShared_7399_ = v_isSharedCheck_7407_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_inc(v_a_7396_);
                                    lean_dec(v___x_7395_);
                                    v___x_7398_ = lean_box(0);
                                    v_isShared_7399_ = v_isSharedCheck_7407_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_7382_);
                                lean_dec(v_mvarId_7381_);
                                v_a_7408_ = lean_ctor_get(v___x_7395_, 0);
                                v_isSharedCheck_7415_ = (!lean_is_exclusive(v___x_7395_)) as u8;
                                if v_isSharedCheck_7415_ == 0 {
                                    v___x_7410_ = v___x_7395_;
                                    v_isShared_7411_ = v_isSharedCheck_7415_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_inc(v_a_7408_);
                                    lean_dec(v___x_7395_);
                                    v___x_7410_ = lean_box(0);
                                    v_isShared_7411_ = v_isSharedCheck_7415_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_7382_);
                            lean_dec(v_mvarId_7381_);
                            v_a_7416_ = lean_ctor_get(v___x_7392_, 0);
                            v_isSharedCheck_7423_ = (!lean_is_exclusive(v___x_7392_)) as u8;
                            if v_isSharedCheck_7423_ == 0 {
                                v___x_7418_ = v___x_7392_;
                                v_isShared_7419_ = v_isSharedCheck_7423_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_7416_);
                                lean_dec(v___x_7392_);
                                v___x_7418_ = lean_box(0);
                                v_isShared_7419_ = v_isSharedCheck_7423_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v___x_7382_);
                        lean_dec(v_mvarId_7381_);
                        v_a_7424_ = lean_ctor_get(v___x_7389_, 0);
                        v_isSharedCheck_7431_ = (!lean_is_exclusive(v___x_7389_)) as u8;
                        if v_isSharedCheck_7431_ == 0 {
                            v___x_7426_ = v___x_7389_;
                            v_isShared_7427_ = v_isSharedCheck_7431_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_7424_);
                            lean_dec(v___x_7389_);
                            v___x_7426_ = lean_box(0);
                            v_isShared_7427_ = v_isSharedCheck_7431_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_7382_);
                    lean_dec(v_mvarId_7381_);
                    return v___x_7388_;
                }
            }
            1 => {
                v___x_7400_ = (lean_unbox(v_a_7396_) as u8);
                lean_dec(v_a_7396_);
                if v___x_7400_ == 0 {
                    lean_del_object(v___x_7398_);
                    v___x_7401_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_MVarId_inferInstance___lam__0___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_MVarId_inferInstance___lam__0___closed__3_once
                        ),
                        _init_l_Lean_MVarId_inferInstance___lam__0___closed__3,
                    );
                    v___x_7402_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_7382_,
                        v_mvarId_7381_,
                        v___x_7401_,
                        v___y_7383_,
                        v___y_7384_,
                        v___y_7385_,
                        v___y_7386_,
                    );
                    return v___x_7402_;
                } else {
                    lean_dec(v___x_7382_);
                    lean_dec(v_mvarId_7381_);
                    v___x_7403_ = lean_box(0);
                    if v_isShared_7399_ == 0 {
                        lean_ctor_set(v___x_7398_, 0, v___x_7403_);
                        v___x_7405_ = v___x_7398_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_7406_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_7406_, 0, v___x_7403_);
                        v___x_7405_ = v_reuseFailAlloc_7406_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_7405_;
            }
            3 => {
                if v_isShared_7411_ == 0 {
                    v___x_7413_ = v___x_7410_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7414_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7414_, 0, v_a_7408_);
                    v___x_7413_ = v_reuseFailAlloc_7414_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7413_;
            }
            5 => {
                if v_isShared_7419_ == 0 {
                    v___x_7421_ = v___x_7418_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7422_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7422_, 0, v_a_7416_);
                    v___x_7421_ = v_reuseFailAlloc_7422_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7421_;
            }
            7 => {
                if v_isShared_7427_ == 0 {
                    v___x_7429_ = v___x_7426_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7430_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7430_, 0, v_a_7424_);
                    v___x_7429_ = v_reuseFailAlloc_7430_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_7429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_inferInstance___lam__0___boxed(
    mut v_mvarId_7432_: *mut LeanObject,
    mut v___x_7433_: *mut LeanObject,
    mut v___y_7434_: *mut LeanObject,
    mut v___y_7435_: *mut LeanObject,
    mut v___y_7436_: *mut LeanObject,
    mut v___y_7437_: *mut LeanObject,
    mut v___y_7438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7439_: *mut LeanObject = core::ptr::null_mut();
    v_res_7439_ = l_Lean_MVarId_inferInstance___lam__0(
        v_mvarId_7432_,
        v___x_7433_,
        v___y_7434_,
        v___y_7435_,
        v___y_7436_,
        v___y_7437_,
    );
    lean_dec(v___y_7437_);
    lean_dec_ref(v___y_7436_);
    lean_dec(v___y_7435_);
    lean_dec_ref(v___y_7434_);
    return v_res_7439_;
}
pub unsafe fn l_Lean_MVarId_inferInstance(
    mut v_mvarId_7443_: *mut LeanObject,
    mut v_a_7444_: *mut LeanObject,
    mut v_a_7445_: *mut LeanObject,
    mut v_a_7446_: *mut LeanObject,
    mut v_a_7447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_7450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7451_: *mut LeanObject = core::ptr::null_mut();
    v___x_7449_ = l_Lean_MVarId_inferInstance___closed__1;
    lean_inc(v_mvarId_7443_);
    v___f_7450_ = lean_alloc_closure(
        l_Lean_MVarId_inferInstance___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    lean_closure_set(v___f_7450_, 0, v_mvarId_7443_);
    lean_closure_set(v___f_7450_, 1, v___x_7449_);
    v___x_7451_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_admit_spec__1___redArg(
        v_mvarId_7443_,
        v___f_7450_,
        v_a_7444_,
        v_a_7445_,
        v_a_7446_,
        v_a_7447_,
    );
    return v___x_7451_;
}
pub unsafe fn l_Lean_MVarId_inferInstance___boxed(
    mut v_mvarId_7452_: *mut LeanObject,
    mut v_a_7453_: *mut LeanObject,
    mut v_a_7454_: *mut LeanObject,
    mut v_a_7455_: *mut LeanObject,
    mut v_a_7456_: *mut LeanObject,
    mut v_a_7457_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7458_: *mut LeanObject = core::ptr::null_mut();
    v_res_7458_ =
        l_Lean_MVarId_inferInstance(v_mvarId_7452_, v_a_7453_, v_a_7454_, v_a_7455_, v_a_7456_);
    lean_dec(v_a_7456_);
    lean_dec_ref(v_a_7455_);
    lean_dec(v_a_7454_);
    lean_dec_ref(v_a_7453_);
    return v_res_7458_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorIdx(
    mut v_x_7459_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_7459_) {
        0 => {
            let mut v___x_7460_: *mut LeanObject = core::ptr::null_mut();
            v___x_7460_ = lean_unsigned_to_nat(0);
            return v___x_7460_;
        }
        1 => {
            let mut v___x_7461_: *mut LeanObject = core::ptr::null_mut();
            v___x_7461_ = lean_unsigned_to_nat(1);
            return v___x_7461_;
        }
        _ => {
            let mut v___x_7462_: *mut LeanObject = core::ptr::null_mut();
            v___x_7462_ = lean_unsigned_to_nat(2);
            return v___x_7462_;
        }
    }
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorIdx___boxed(
    mut v_x_7463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7464_: *mut LeanObject = core::ptr::null_mut();
    v_res_7464_ = l_Lean_Meta_TacticResultCNM_ctorIdx(v_x_7463_);
    lean_dec(v_x_7463_);
    return v_res_7464_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorElim___redArg(
    mut v_t_7465_: *mut LeanObject,
    mut v_k_7466_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_7465_) == 2 {
        let mut v_mvarId_7467_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_7468_: *mut LeanObject = core::ptr::null_mut();
        v_mvarId_7467_ = lean_ctor_get(v_t_7465_, 0);
        lean_inc(v_mvarId_7467_);
        lean_dec_ref_known(v_t_7465_, 1);
        v___x_7468_ = lean_apply_1(v_k_7466_, v_mvarId_7467_);
        return v___x_7468_;
    } else {
        lean_dec(v_t_7465_);
        return v_k_7466_;
    }
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorElim(
    mut v_motive_7469_: *mut LeanObject,
    mut v_ctorIdx_7470_: *mut LeanObject,
    mut v_t_7471_: *mut LeanObject,
    mut v_h_7472_: *mut LeanObject,
    mut v_k_7473_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7474_: *mut LeanObject = core::ptr::null_mut();
    v___x_7474_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7471_, v_k_7473_);
    return v___x_7474_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_ctorElim___boxed(
    mut v_motive_7475_: *mut LeanObject,
    mut v_ctorIdx_7476_: *mut LeanObject,
    mut v_t_7477_: *mut LeanObject,
    mut v_h_7478_: *mut LeanObject,
    mut v_k_7479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7480_: *mut LeanObject = core::ptr::null_mut();
    v_res_7480_ = l_Lean_Meta_TacticResultCNM_ctorElim(
        v_motive_7475_,
        v_ctorIdx_7476_,
        v_t_7477_,
        v_h_7478_,
        v_k_7479_,
    );
    lean_dec(v_ctorIdx_7476_);
    return v_res_7480_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_closed_elim___redArg(
    mut v_t_7481_: *mut LeanObject,
    mut v_closed_7482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7483_: *mut LeanObject = core::ptr::null_mut();
    v___x_7483_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7481_, v_closed_7482_);
    return v___x_7483_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_closed_elim(
    mut v_motive_7484_: *mut LeanObject,
    mut v_t_7485_: *mut LeanObject,
    mut v_h_7486_: *mut LeanObject,
    mut v_closed_7487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7488_: *mut LeanObject = core::ptr::null_mut();
    v___x_7488_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7485_, v_closed_7487_);
    return v___x_7488_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_noChange_elim___redArg(
    mut v_t_7489_: *mut LeanObject,
    mut v_noChange_7490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7491_: *mut LeanObject = core::ptr::null_mut();
    v___x_7491_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7489_, v_noChange_7490_);
    return v___x_7491_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_noChange_elim(
    mut v_motive_7492_: *mut LeanObject,
    mut v_t_7493_: *mut LeanObject,
    mut v_h_7494_: *mut LeanObject,
    mut v_noChange_7495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7496_: *mut LeanObject = core::ptr::null_mut();
    v___x_7496_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7493_, v_noChange_7495_);
    return v___x_7496_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_modified_elim___redArg(
    mut v_t_7497_: *mut LeanObject,
    mut v_modified_7498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7499_: *mut LeanObject = core::ptr::null_mut();
    v___x_7499_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7497_, v_modified_7498_);
    return v___x_7499_;
}
pub unsafe fn l_Lean_Meta_TacticResultCNM_modified_elim(
    mut v_motive_7500_: *mut LeanObject,
    mut v_t_7501_: *mut LeanObject,
    mut v_h_7502_: *mut LeanObject,
    mut v_modified_7503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7504_: *mut LeanObject = core::ptr::null_mut();
    v___x_7504_ = l_Lean_Meta_TacticResultCNM_ctorElim___redArg(v_t_7501_, v_modified_7503_);
    return v___x_7504_;
}
pub unsafe fn l_Lean_MVarId_isSubsingleton(
    mut v_g_7508_: *mut LeanObject,
    mut v_a_7509_: *mut LeanObject,
    mut v_a_7510_: *mut LeanObject,
    mut v_a_7511_: *mut LeanObject,
    mut v_a_7512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_7515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7516_: u8 = 0;
    let mut v___x_7517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7522_: u8 = 0;
    let mut v___x_7523_: u8 = 0;
    let mut v___x_7524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7536_: u8 = 0;
    let mut v___x_7537_: u8 = 0;
    let mut v___x_7538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7542_: u8 = 0;
    let mut v_unused_7543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7546_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7524_ =
                    l_Lean_MVarId_getType(v_g_7508_, v_a_7509_, v_a_7510_, v_a_7511_, v_a_7512_);
                if lean_obj_tag(v___x_7524_) == 0 {
                    v_a_7525_ = lean_ctor_get(v___x_7524_, 0);
                    lean_inc(v_a_7525_);
                    lean_dec_ref_known(v___x_7524_, 1);
                    v___x_7526_ = l_Lean_MVarId_isSubsingleton___closed__1;
                    v___x_7527_ = lean_unsigned_to_nat(1);
                    v___x_7528_ = lean_mk_empty_array_with_capacity(v___x_7527_);
                    v___x_7529_ = lean_array_push(v___x_7528_, v_a_7525_);
                    v___x_7530_ = l_Lean_Meta_mkAppM(
                        v___x_7526_,
                        v___x_7529_,
                        v_a_7509_,
                        v_a_7510_,
                        v_a_7511_,
                        v_a_7512_,
                    );
                    if lean_obj_tag(v___x_7530_) == 0 {
                        v_a_7531_ = lean_ctor_get(v___x_7530_, 0);
                        lean_inc(v_a_7531_);
                        lean_dec_ref_known(v___x_7530_, 1);
                        v___x_7532_ = lean_box(0);
                        v___x_7533_ = l_Lean_Meta_synthInstance(
                            v_a_7531_,
                            v___x_7532_,
                            v_a_7509_,
                            v_a_7510_,
                            v_a_7511_,
                            v_a_7512_,
                        );
                        if lean_obj_tag(v___x_7533_) == 0 {
                            v_isSharedCheck_7542_ = (!lean_is_exclusive(v___x_7533_)) as u8;
                            if v_isSharedCheck_7542_ == 0 {
                                v_unused_7543_ = lean_ctor_get(v___x_7533_, 0);
                                lean_dec(v_unused_7543_);
                                v___x_7535_ = v___x_7533_;
                                v_isShared_7536_ = v_isSharedCheck_7542_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_7533_);
                                v___x_7535_ = lean_box(0);
                                v_isShared_7536_ = v_isSharedCheck_7542_;
                                state = 3;
                                continue;
                            }
                        } else {
                            v_a_7544_ = lean_ctor_get(v___x_7533_, 0);
                            lean_inc(v_a_7544_);
                            lean_dec_ref_known(v___x_7533_, 1);
                            v_a_7521_ = v_a_7544_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v_a_7545_ = lean_ctor_get(v___x_7530_, 0);
                        lean_inc(v_a_7545_);
                        lean_dec_ref_known(v___x_7530_, 1);
                        v_a_7521_ = v_a_7545_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_7546_ = lean_ctor_get(v___x_7524_, 0);
                    lean_inc(v_a_7546_);
                    lean_dec_ref_known(v___x_7524_, 1);
                    v_a_7521_ = v_a_7546_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                if v___y_7516_ == 0 {
                    lean_dec_ref(v___y_7515_);
                    v___x_7517_ = lean_box((v___y_7516_) as usize);
                    v___x_7518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7518_, 0, v___x_7517_);
                    return v___x_7518_;
                } else {
                    v___x_7519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_7519_, 0, v___y_7515_);
                    return v___x_7519_;
                }
            }
            2 => {
                v___x_7522_ = l_Lean_Exception_isInterrupt(v_a_7521_);
                if v___x_7522_ == 0 {
                    lean_inc_ref(v_a_7521_);
                    v___x_7523_ = l_Lean_Exception_isRuntime(v_a_7521_);
                    v___y_7515_ = v_a_7521_;
                    v___y_7516_ = v___x_7523_;
                    state = 1;
                    continue;
                } else {
                    v___y_7515_ = v_a_7521_;
                    v___y_7516_ = v___x_7522_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_7537_ = 1;
                v___x_7538_ = lean_box((v___x_7537_) as usize);
                if v_isShared_7536_ == 0 {
                    lean_ctor_set(v___x_7535_, 0, v___x_7538_);
                    v___x_7540_ = v___x_7535_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7541_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7541_, 0, v___x_7538_);
                    v___x_7540_ = v_reuseFailAlloc_7541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_isSubsingleton___boxed(
    mut v_g_7547_: *mut LeanObject,
    mut v_a_7548_: *mut LeanObject,
    mut v_a_7549_: *mut LeanObject,
    mut v_a_7550_: *mut LeanObject,
    mut v_a_7551_: *mut LeanObject,
    mut v_a_7552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7553_: *mut LeanObject = core::ptr::null_mut();
    v_res_7553_ =
        l_Lean_MVarId_isSubsingleton(v_g_7547_, v_a_7548_, v_a_7549_, v_a_7550_, v_a_7551_);
    lean_dec(v_a_7551_);
    lean_dec_ref(v_a_7550_);
    lean_dec(v_a_7549_);
    lean_dec_ref(v_a_7548_);
    return v_res_7553_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_()
-> *mut LeanObject {
    let mut v___x_7571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7574_: *mut LeanObject = core::ptr::null_mut();
    v___x_7571_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_;
    v___x_7572_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_;
    v___x_7573_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_;
    v___x_7574_ = l_Lean_Option_register___at___00__private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4__spec__0(v___x_7571_, v___x_7572_, v___x_7573_);
    return v___x_7574_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4____boxed(
    mut v_a_7575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7576_: *mut LeanObject = core::ptr::null_mut();
    v_res_7576_ = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
    return v_res_7576_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_ForEachExprWhere(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_2566314605____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_debug_terminalTacticsAsSorry = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_debug_terminalTacticsAsSorry);
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_1901113268____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Util_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Util_3824588779____hygCtx___hyg_4_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_tactic_skipAssignedInstances = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_tactic_skipAssignedInstances);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Util(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_ForEachExprWhere(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_PPGoal(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_AppBuilder(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Util(builtin);
}
